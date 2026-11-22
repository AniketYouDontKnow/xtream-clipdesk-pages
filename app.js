'use strict';

const $ = (id) => document.getElementById(id);
const video = $('video');
const timeline = $('timeline');
const dialog = $('vpn-dialog');
const onPages = !!document.querySelector('meta[name="clipdesk-hosting"][content="pages"]');
const topbarActions = document.querySelector('.topbar-actions');
const PAGE_SIZE = 120;
const MIN_CLIP = 0.25;
const MAX_CLIP = 120;
const GUIDE_REFRESH_MS = 60_000;
const guideDay = new Intl.DateTimeFormat(undefined, { weekday: 'short', month: 'short', day: 'numeric' });
const guideTime = new Intl.DateTimeFormat(undefined, { hour: 'numeric', minute: '2-digit' });
const expiryDate = new Intl.DateTimeFormat(undefined, { dateStyle: 'medium' });
const expiryCalendarDate = new Intl.DateTimeFormat(undefined, { dateStyle: 'medium', timeZone: 'UTC' });
const guideCache = new Map();
const downloadLinks = new Set();
const keyRejected = 'The backend rejected the owner access key. Check the key and reconnect.';

let state = { portal: null, stream: { status: 'idle' }, channelId: null };
let remoteSession = null;
let channelsById = new Map();
let channelsShown = PAGE_SIZE;
let initialized = false;
let offline = false;
let operation = null;
let revision = 0;
let hls;
let mediaId = null;
let mediaFragments = [];
let activeFragment = null;
let fragmentsBySequence = new Map();
let fragmentsByName = new Map();
let playerError = '';
let scrubbing = false;
let markIn = null;
let markOut = null;
let previewEnd = null;
let exporting = false;
let editorNotice = '';
let editorTone = '';
let profiles = [];
let vpnLoading = false;
let vpnRevision = 0;
let vpnNotice = '';
let vpnError = '';
let pinnedGuideChannel = null;
let guideRequest = null;
let guideListKey = '';

video.muted = true;

function remoteLocked() {
  return onPages && !remoteSession?.authorized;
}

function backendOrigin(raw) {
  let address;
  try {
    address = new URL(raw);
  } catch {
    throw new Error('Enter the full HTTPS backend URL.');
  }
  const localTest = location.protocol === 'http:' && ['127.0.0.1', 'localhost', '[::1]'].includes(location.hostname) &&
    address.protocol === 'http:' && address.hostname === '127.0.0.1' && address.port;
  if (address.protocol !== 'https:' && !localTest) throw new Error('The backend URL needs HTTPS.');
  if (address.username || address.password || address.pathname !== '/' || address.search || address.hash) {
    throw new Error('Enter only the backend origin, including the port if it uses one.');
  }
  if (address.origin === location.origin) throw new Error('Enter the backend URL instead of this page’s URL.');
  return address.origin;
}

async function request(path, options = {}) {
  const session = remoteSession;
  let address = path;
  let settings = { cache: 'no-store', ...options };
  if (onPages) {
    if (!session) throw new Error('Connect to your backend first.');
    const target = new URL(path, session.origin);
    if (target.origin !== session.origin || !target.pathname.startsWith('/api/')) {
      throw new Error('The app did not recognize this backend request.');
    }
    address = target.href;
    const headers = new Headers(options.headers);
    headers.set('Authorization', `Bearer ${session.key}`);
    const signal = options.signal
      ? AbortSignal.any([session.controller.signal, options.signal])
      : session.controller.signal;
    settings = { ...settings, headers, signal, credentials: 'omit', redirect: 'error', referrerPolicy: 'no-referrer' };
  }
  const response = await fetch(address, settings);
  if (!response.ok) {
    const error = await response.json().catch(() => ({}));
    const denied = session && response.status === 401 && (!session.authorized || error?.code === 'remote_unauthorized' ||
      response.headers.get('WWW-Authenticate')?.toLowerCase().startsWith('bearer'));
    if (denied) {
      if (session === remoteSession && session.authorized) lockRemote(keyRejected, { preserveAddress: true });
      throw new Error(keyRejected);
    }
    throw new Error(error?.error || `The app could not complete the request (${response.status}).`);
  }
  return response;
}

function post(path, body) {
  return request(path, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

function setMessage(id, text, tone = '') {
  const element = $(id);
  if (element.textContent !== text) element.textContent = text;
  if (element.dataset.tone !== tone) element.dataset.tone = tone;
  if (element.hidden !== !text) element.hidden = !text;
}

function setStatus(id, text, tone = '') {
  const element = $(id);
  element.lastElementChild.textContent = text;
  element.dataset.tone = tone;
}

function setButtonLabel(element, label) {
  element.setAttribute('aria-label', label);
  element.title = label;
}

function updateLoginForm() {
  const stalker = $('login-form').elements.type.value === 'stalker';
  $('xtream-credentials').hidden = stalker;
  $('connection-options').hidden = stalker;
  $('stalker-credentials').hidden = !stalker;
  $('username').disabled = stalker;
  $('password').disabled = stalker;
  $('format').disabled = stalker;
  $('mac').disabled = !stalker;
  $('stalker-fields').disabled = !stalker;
  $('portal-url').placeholder = stalker ? 'https://portal.example.com/c/' : 'https://portal.example.com:8080';
}

function stalkerCredentials(fields) {
  const credentials = {
    mac: fields.mac.trim(),
    label: fields.label.trim(),
    serialNumber: fields.serialNumber.trim(),
    deviceId: fields.deviceId.trim(),
    deviceId2: fields.deviceId2.trim(),
    username: fields.username,
    password: fields.password,
  };
  return Object.fromEntries(Object.entries(credentials).filter(([, value]) => value));
}

function timeLabel(seconds, precise = false) {
  const hundredths = Math.round(Math.max(0, seconds) * 100);
  const time = Math.floor(hundredths / 100);
  const hours = Math.floor(time / 3600);
  const minutes = Math.floor(time / 60) % 60;
  const digits = (number) => String(number).padStart(2, '0');
  const value = hours ? `${hours}:${digits(minutes)}:${digits(time % 60)}` : `${digits(minutes)}:${digits(time % 60)}`;
  return precise ? `${value}.${digits(hundredths % 100)}` : value;
}

function bufferBounds() {
  const { oldest, edge } = state.stream;
  return Number.isFinite(oldest) && Number.isFinite(edge) && edge > oldest ? { oldest, edge } : null;
}

function clamp(value, min, max) {
  return Math.min(Math.max(value, min), max);
}

function joinStreamFragments(fragment) {
  if (!fragment) return null;
  return fragmentsBySequence.get(Number(fragment.sn)) || fragmentsByName.get(fragment.relurl?.split('/').at(-1)) || null;
}

function dvrPosition() {
  if (!mediaId || video.readyState < HTMLMediaElement.HAVE_METADATA) return null;
  const bounds = bufferBounds();
  if (!bounds) return null;

  if (!hls) {
    const { seekable } = video;
    if (!seekable.length) return null;
    return clamp(bounds.edge - (seekable.end(seekable.length - 1) - video.currentTime), bounds.oldest, bounds.edge);
  }

  const currentTime = video.currentTime;
  const containing = mediaFragments.find((fragment) => currentTime >= fragment.start && currentTime <= fragment.start + fragment.duration);
  const reference = [containing, activeFragment].find((fragment) => joinStreamFragments(fragment))
    || mediaFragments.find((fragment) => joinStreamFragments(fragment));
  const match = joinStreamFragments(reference);
  if (!match) return null;
  return clamp(match.start + currentTime - reference.start, bounds.oldest, bounds.edge);
}

function seekTo(position) {
  const { seekable } = video;
  const bounds = bufferBounds();
  if (!mediaId || !bounds || !seekable.length) return false;

  const target = clamp(position, bounds.oldest, bounds.edge - 0.05);
  let mediaTime;
  if (!hls) {
    mediaTime = seekable.end(seekable.length - 1) - (bounds.edge - target);
  } else {
    const reference = mediaFragments.find((fragment) => {
      const match = joinStreamFragments(fragment);
      return match && target >= match.start - 0.001 && target < match.start + match.duration;
    }) || mediaFragments.find((fragment) => joinStreamFragments(fragment));
    const match = joinStreamFragments(reference);
    if (!match) return false;
    mediaTime = reference.start + target - match.start;
  }

  const index = Array.from({ length: seekable.length }, (_, i) => i).find((i) => seekable.end(i) > mediaTime) ?? seekable.length - 1;
  video.currentTime = clamp(mediaTime, seekable.start(index), seekable.end(index) - 0.01);
  return true;
}

function resetPlayer() {
  mediaId = null;
  mediaFragments = [];
  activeFragment = null;
  playerError = '';
  if (hls) {
    hls.destroy();
    hls = undefined;
  }
  video.pause();
  video.removeAttribute('src');
  video.load();
}

function configureRemoteMedia(xhr, url, session) {
  const target = new URL(url, session.origin);
  const mediaPath = /^\/media\/[a-f\d-]{16,64}\/[A-Za-z0-9._-]{1,100}$/;
  if (session !== remoteSession || !session.authorized || target.origin !== session.origin ||
    !mediaPath.test(target.pathname) || target.search || target.hash || target.username || target.password) {
    throw new Error('The app rejected an unexpected media address.');
  }
  if (xhr.readyState === XMLHttpRequest.UNSENT) xhr.open('GET', target.href, true);
  xhr.withCredentials = false;
  xhr.setRequestHeader('Authorization', `Bearer ${session.key}`);
  xhr.addEventListener('readystatechange', () => {
    if (xhr.readyState !== XMLHttpRequest.HEADERS_RECEIVED) return;
    if (xhr.responseURL !== target.href) xhr.abort();
    else if (xhr.status === 401) {
      queueMicrotask(() => { if (session === remoteSession) lockRemote(keyRejected, { preserveAddress: true }); });
    }
  });
}

function attachPlayer(id) {
  resetPlayer();
  mediaId = id;
  const session = remoteSession;
  const path = `/media/${encodeURIComponent(id)}/index.m3u8`;
  const address = session ? new URL(path, session.origin).href : path;
  if (window.Hls?.isSupported()) {
    const options = { enableWorker: true };
    if (session) {
      options.lowLatencyMode = false;
      options.xhrSetup = (xhr, url) => configureRemoteMedia(xhr, url, session);
    }
    const player = new window.Hls(options);
    hls = player;
    let recoveredMediaError = false;
    let networkRetries = 0;
    player.on(window.Hls.Events.LEVEL_UPDATED, (_event, data) => {
      if (hls !== player) return;
      mediaFragments = data.details.fragments;
      renderEditor();
    });
    player.on(window.Hls.Events.FRAG_CHANGED, (_event, data) => {
      if (hls !== player) return;
      activeFragment = data.frag;
    });
    player.on(window.Hls.Events.FRAG_BUFFERED, () => { networkRetries = 0; });
    player.on(window.Hls.Events.MANIFEST_PARSED, () => {
      if (hls === player) video.play().catch(() => {});
    });
    player.on(window.Hls.Events.ERROR, (_event, data) => {
      if (hls !== player || !data.fatal) return;
      if (data.type === window.Hls.ErrorTypes.MEDIA_ERROR && !recoveredMediaError) {
        recoveredMediaError = true;
        player.recoverMediaError();
      } else if (data.type === window.Hls.ErrorTypes.NETWORK_ERROR && networkRetries < 2) {
        networkRetries += 1;
        setTimeout(() => { if (hls === player) player.startLoad(); }, 900);
      } else {
        playerError = 'The browser lost playback. Retry the player or export from the available buffer.';
        renderStream();
      }
    });
    player.loadSource(address);
    player.attachMedia(video);
  } else if (!onPages && video.canPlayType('application/vnd.apple.mpegurl')) {
    video.src = address;
    video.play().catch(() => {});
  } else {
    playerError = onPages
      ? 'Remote live preview needs a browser that supports HLS.js. Try a current version of Microsoft Edge or Chrome.'
      : 'This browser cannot play the live preview. Open the app in Microsoft Edge, Chrome, or another HLS-capable browser.';
  }
}

function renderChannels(rebuildCategories = false) {
  const connected = !!state.portal;
  const channels = state.portal?.channels || [];
  const categoryInput = $('category');
  $('channel-search').disabled = !connected;
  categoryInput.disabled = !connected;
  if (rebuildCategories) {
    const previous = categoryInput.value;
    const categories = Array.from(new Set(channels.map((channel) => channel.category).filter(Boolean)));
    categories.sort((first, second) => first.localeCompare(second, undefined, { numeric: true }));
    categoryInput.replaceChildren(new Option('All categories', ''), ...categories.map((category) => new Option(category, category)));
    if (categories.includes(previous)) categoryInput.value = previous;
  }

  const query = $('channel-search').value.trim().toLowerCase();
  const category = categoryInput.value;
  const matching = channels.filter((channel) => (!category || channel.category === category) && (!query || channel.name.toLowerCase().includes(query)));
  const list = document.createDocumentFragment();
  for (const channel of matching.slice(0, channelsShown)) {
    const item = document.createElement('li');
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'channel-button';
    button.dataset.channelId = channel.id;
    button.setAttribute('aria-current', String(channel.id === state.channelId));
    button.disabled = !!operation || exporting;

    const initial = document.createElement('span');
    initial.className = 'channel-initial';
    initial.setAttribute('aria-hidden', 'true');
    const initials = channel.name.match(/[\p{L}\p{N}]+/gu) || [];
    initial.textContent = initials.slice(0, 2).map((word) => Array.from(word)[0]).join('').toUpperCase() || '•';

    const info = document.createElement('span');
    info.className = 'channel-info';
    const name = document.createElement('span');
    name.className = 'channel-name';
    name.textContent = channel.name;
    name.title = channel.name;
    info.append(name);
    if (channel.category) {
      const subtitle = document.createElement('span');
      subtitle.className = 'channel-item-category';
      subtitle.textContent = channel.category;
      info.append(subtitle);
    }
    button.append(initial, info);

    const guideButton = document.createElement('button');
    guideButton.type = 'button';
    guideButton.className = 'button icon-button channel-guide';
    guideButton.dataset.guideChannel = channel.id;
    guideButton.setAttribute('aria-pressed', String(channel.id === selectedGuideChannel()));
    setButtonLabel(guideButton, `Guide for ${channel.name}`);
    const guideIcon = document.createElement('span');
    guideIcon.className = 'guide-icon';
    guideIcon.setAttribute('aria-hidden', 'true');
    guideButton.append(guideIcon);
    item.append(button, guideButton);
    list.append(item);
  }
  $('channel-list').replaceChildren(list);
  $('channel-count').textContent = connected ? `${matching.length.toLocaleString()} ${matching.length === 1 ? 'channel' : 'channels'}` : '';
  $('channel-more').hidden = matching.length <= channelsShown;
  $('channel-empty').hidden = matching.length > 0;
  $('channel-empty').textContent = connected
    ? (channels.length ? 'No channels match these filters.' : 'This portal returned no live channels.')
    : 'Connect to a portal to see your live channels.';
}

function selectedGuideChannel() {
  return pinnedGuideChannel || state.channelId;
}

function renderGuide() {
  const channelId = selectedGuideChannel();
  const channel = channelsById.get(channelId);
  const entry = guideCache.get(channelId);
  const loading = guideRequest?.channelId === channelId;
  const now = Date.now();
  const programmes = (entry?.programmes || []).filter((programme) => programme.end > now);
  const current = programmes.find((programme) => programme.start <= now);
  const liveProgramme = guideCache.get(state.channelId)?.programmes.find((programme) => programme.start <= now && programme.end > now);
  $('guide-panel').hidden = !state.portal;
  $('guide-channel-label').textContent = channel?.name || 'Open a channel’s guide from the channel list.';
  $('guide-follow').hidden = !pinnedGuideChannel || !state.channelId;
  $('guide-refresh').hidden = !channel;
  $('guide-refresh').disabled = loading || operation === 'vpn';
  $('now-playing').hidden = !liveProgramme;
  $('now-playing-title').textContent = liveProgramme?.title || '';

  for (const button of $('channel-list').querySelectorAll('[data-guide-channel]')) {
    button.setAttribute('aria-pressed', String(button.dataset.guideChannel === channelId));
  }

  let message = '';
  let tone = '';
  if (channel && operation === 'vpn') message = 'Waiting for the VPN route to update…';
  else if (loading && !programmes.length) message = 'Loading programme listings…';
  else if (!loading && entry?.error) {
    message = entry.error;
    tone = 'error';
  } else if (channel && !programmes.length) message = 'No current or upcoming listings for this channel.';
  setMessage('guide-message', message, tone);
  const listKey = JSON.stringify([channelId, entry?.checkedAt, programmes.length, current?.start]);
  if (guideListKey === listKey) return;
  guideListKey = listKey;

  const schedule = document.createDocumentFragment();
  let day = '';
  for (const programme of programmes) {
    const programmeDay = guideDay.format(Math.max(programme.start, now));
    if (programmeDay !== day) {
      day = programmeDay;
      const heading = document.createElement('li');
      heading.className = 'guide-day';
      heading.textContent = day;
      schedule.append(heading);
    }
    const item = document.createElement('li');
    item.className = 'guide-programme';
    item.dataset.current = String(programme === current);
    if (programme === current) item.setAttribute('aria-current', 'time');
    const range = document.createElement('div');
    range.className = 'guide-programme-time';
    const start = document.createElement('time');
    start.dateTime = new Date(programme.start).toISOString();
    start.textContent = guideTime.format(programme.start);
    const end = document.createElement('time');
    end.dateTime = new Date(programme.end).toISOString();
    end.textContent = guideTime.format(programme.end);
    range.append(start, ' – ', end);
    range.title = `${new Date(programme.start).toLocaleString()} – ${new Date(programme.end).toLocaleString()}`;
    const info = document.createElement('div');
    info.className = 'guide-programme-info';
    const title = document.createElement('span');
    title.className = 'guide-programme-title';
    title.textContent = programme.title;
    info.append(title);
    if (programme === current) {
      const badge = document.createElement('span');
      badge.className = 'guide-current';
      badge.textContent = 'On now';
      info.append(badge);
    }
    if (programme.description) {
      const description = document.createElement('p');
      description.className = 'guide-programme-description';
      description.textContent = programme.description;
      info.append(description);
    }
    item.append(range, info);
    schedule.append(item);
  }
  const list = $('guide-list');
  const scroll = list.dataset.channel === channelId ? list.scrollTop : 0;
  list.dataset.channel = channelId || '';
  list.replaceChildren(schedule);
  list.scrollTop = scroll;
}

function resetGuide({ clearSelection = false } = {}) {
  guideRequest?.controller.abort();
  guideRequest = null;
  guideCache.clear();
  if (clearSelection) pinnedGuideChannel = null;
}

async function refreshGuide(force = false) {
  const channelId = selectedGuideChannel();
  const previous = guideCache.get(channelId);
  if (guideRequest && guideRequest.channelId !== channelId) {
    guideRequest.controller.abort();
    guideRequest = null;
  }
  if (!channelId || !channelsById.has(channelId) || operation === 'vpn' ||
    guideRequest || (!force && previous && Date.now() - previous.checkedAt < GUIDE_REFRESH_MS)) {
    renderGuide();
    return;
  }

  const controller = new AbortController();
  guideRequest = { channelId, controller };
  renderGuide();
  try {
    const response = await request(`/api/epg?channelId=${encodeURIComponent(channelId)}`, { signal: controller.signal });
    const guide = await response.json();
    if (controller.signal.aborted || guide.channelId !== channelId) return;
    const programmes = (guide.programmes || []).filter((programme) => typeof programme.title === 'string' &&
      Number.isFinite(programme.start) && Number.isFinite(programme.end) && Math.abs(programme.start) < 8.64e15 &&
      Math.abs(programme.end) < 8.64e15 && programme.end > programme.start).sort((first, second) => first.start - second.start);
    guideCache.set(channelId, { programmes, checkedAt: Date.now() });
    if (guideCache.size > 24) {
      const oldest = [...guideCache.keys()].find((id) => id !== channelId && id !== state.channelId);
      guideCache.delete(oldest);
    }
  } catch (error) {
    if (!controller.signal.aborted) guideCache.set(channelId, { programmes: previous?.programmes || [], checkedAt: Date.now(), error: error.message });
  } finally {
    if (guideRequest?.controller === controller) {
      guideRequest = null;
      renderGuide();
    }
  }
}

function renderHeader() {
  renderBackend();
  const connected = !!state.portal;
  const verifying = operation === 'login';
  $('workspace').dataset.connected = String(connected);
  $('connect-screen').hidden = connected;
  $('logout').hidden = !connected;
  $('logout').disabled = !!operation || exporting;
  $('login-types').disabled = verifying;
  $('login-form').setAttribute('aria-busy', String(verifying));
  $('login-button').disabled = !!operation;
  $('login-button').dataset.pending = String(verifying);
  $('login-button').textContent = verifying ? 'Verifying access…' : 'Connect portal';
  $('portal-status').title = connected ? `${state.portal.type === 'stalker' ? 'MAG / Stalker' : 'Xtream Codes'} portal` : 'Portal connection';
  const expiresAt = state.portal?.expiresAt;
  const expiresOn = state.portal?.expiresOn;
  const expiry = $('portal-expiry');
  expiry.hidden = !Number.isFinite(expiresAt) || expiresAt <= 0 || expiresAt >= 8.64e15;
  if (!expiry.hidden) {
    expiry.dateTime = expiresOn ?? new Date(expiresAt).toISOString();
    const formatter = expiresOn ? expiryCalendarDate : expiryDate;
    expiry.textContent = `Expiry ${formatter.format(expiresAt)}`;
  }
  if (offline) {
    setStatus('portal-status', onPages ? 'Backend offline' : 'Local server offline', 'error');
  } else if (connected) {
    setStatus('portal-status', state.portal.label || 'Portal connected', 'positive');
  } else {
    setStatus('portal-status', initialized ? 'Portal offline' : 'Checking connection');
  }
}

function renderBackend() {
  if (!onPages) return;
  const locked = remoteLocked();
  const verifying = locked && !!remoteSession;
  $('workspace').hidden = locked;
  $('backend-screen').hidden = !locked;
  topbarActions.dataset.remoteAuthorized = String(!locked);
  $('workspace').dataset.remoteAuthorized = String(!locked);
  $('backend-lock').hidden = locked;
  $('backend-form').setAttribute('aria-busy', String(verifying));
  $('backend-url').readOnly = verifying;
  $('backend-key').readOnly = verifying;
  $('backend-connect').disabled = verifying;
  $('backend-connect').dataset.pending = String(verifying);
  $('backend-connect').textContent = verifying ? 'Checking access…' : 'Connect backend';
}

function lockRemote(message = '', { preserveAddress = false, focus = true } = {}) {
  if (!onPages) return;
  const session = remoteSession;
  remoteSession = null;
  if (session) {
    session.key = '';
    session.controller.abort();
  }
  revision += 1;
  vpnRevision += 1;
  operation = null;
  exporting = false;
  offline = false;
  profiles = [];
  vpnLoading = false;
  vpnNotice = '';
  vpnError = '';
  resetGuide({ clearSelection: true });
  for (const link of downloadLinks) URL.revokeObjectURL(link);
  downloadLinks.clear();
  $('vpn-profile').replaceChildren();
  if (dialog.open) dialog.close();
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
  $('login-form').reset();
  updateLoginForm();
  $('backend-key').value = '';
  if (!preserveAddress) $('backend-url').value = '';
  for (const id of ['workspace-message', 'login-error', 'vpn-message']) setMessage(id, '');
  applyState({ portal: null, stream: { status: 'idle', id: null }, channelId: null, vpnAvailable: false, vpnNotice: null });
  initialized = false;
  renderVpn();
  setMessage('backend-error', message, 'error');
  if (focus) $(preserveAddress ? 'backend-key' : 'backend-url').focus();
}

async function connectBackend(event) {
  event.preventDefault();
  if (!onPages || remoteSession) return;
  let origin;
  try {
    origin = backendOrigin($('backend-url').value.trim());
  } catch (error) {
    setMessage('backend-error', error.message, 'error');
    return;
  }
  const key = $('backend-key').value.trim();
  if (!key) {
    setMessage('backend-error', 'Enter your owner access key.', 'error');
    return;
  }
  const session = { origin, key, controller: new AbortController(), authorized: false };
  remoteSession = session;
  $('backend-key').value = '';
  setMessage('backend-error', '');
  renderBackend();
  try {
    const response = await request('/api/state', { signal: AbortSignal.timeout(12_000) });
    const next = await response.json();
    if (session !== remoteSession) return;
    if (!next?.stream || !Object.hasOwn(next, 'portal') || !Object.hasOwn(next, 'channelId')) {
      throw new Error('This address did not return Clipdesk backend status.');
    }
    session.authorized = true;
    applyState(next);
    $('backend-lock').focus({ preventScroll: true });
    void loadVpn();
  } catch (error) {
    if (session !== remoteSession) return;
    const connectionFailed = error instanceof TypeError || error instanceof SyntaxError || error.name === 'TimeoutError';
    lockRemote(connectionFailed ? 'Could not reach Clipdesk. Check the backend URL and its allowed Pages origin.' : error.message, { preserveAddress: true });
  }
}

function renderStream() {
  const stream = state.stream;
  const channel = channelsById.get(state.channelId);
  const streamOn = !!stream.id;
  const canPlay = !!mediaId && !playerError;
  const bounds = bufferBounds();

  $('channel-category').textContent = channel?.category || '';
  $('channel-category').hidden = !channel?.category;
  $('workspace-title').textContent = channel?.name || 'Live workspace';
  $('workspace-detail').hidden = !!channel;
  $('stop').hidden = !streamOn || stream.status === 'idle';
  $('stop').disabled = !!operation || exporting;
  const statusLabels = {
    starting: ['Connecting', 'warning'],
    live: ['Live', 'positive'],
    stalled: ['Feed stalled', 'warning'],
    error: ['Feed error', 'error'],
    idle: ['Standby', ''],
  };
  const visibleStatus = stream.status === 'live' && stream.stalled ? 'stalled' : stream.status;
  setStatus('stream-status', ...(statusLabels[visibleStatus] || statusLabels.idle));

  let title = '';
  let detail = '';
  let canRetry = false;
  if (state.portal) {
    if (playerError) {
      title = 'Preview unavailable';
      detail = playerError;
      canRetry = !!channel;
    } else if (stream.status === 'starting') {
      title = 'Starting the live buffer';
      detail = 'The first segments may take a few seconds to arrive.';
    } else if ((stream.status === 'error' || stream.status === 'stalled') && !bounds) {
      title = stream.status === 'error' ? 'The channel stopped' : 'Waiting for the feed';
      detail = stream.error || 'The live buffer has no playable video yet.';
      canRetry = !!channel;
    } else if (!canPlay) {
      title = 'Choose a live channel';
      detail = 'Select a channel to start watching and recording its rolling buffer.';
    }
  }
  $('player-message').hidden = !title;
  $('player-message-title').textContent = title;
  $('player-message-detail').textContent = detail;
  $('player-graphic').dataset.mode = stream.status;
  $('player-retry').hidden = !canRetry;
  $('player-retry').disabled = !!operation || exporting;
  $('player-retry').textContent = playerError && bounds ? 'Retry preview' : 'Retry channel';
  $('play').disabled = !canPlay;
  $('mute').disabled = !canPlay;
  $('fullscreen').disabled = !canPlay || typeof video.closest('.player-panel').requestFullscreen !== 'function';
  renderPlaybackControls();
  renderEditor();
}

function renderPlaybackControls() {
  $('play').dataset.playing = String(!video.paused);
  setButtonLabel($('play'), video.paused ? 'Play' : 'Pause');
  $('mute').dataset.muted = String(video.muted);
  setButtonLabel($('mute'), video.muted ? 'Unmute' : 'Mute');
}

function renderEditor() {
  const bounds = bufferBounds();
  const current = dvrPosition();
  const maySeek = !!bounds && current !== null && !playerError && !operation;
  const duration = markIn !== null && markOut !== null ? markOut - markIn : null;
  const touchesBuffer = bounds && markIn !== null && markOut !== null && markIn >= bounds.oldest && markOut <= bounds.edge;
  const canExport = touchesBuffer && duration >= MIN_CLIP && duration <= MAX_CLIP;
  const position = scrubbing ? Number(timeline.value) : current;
  const showPoint = position !== null ? timeLabel(position) : '—';
  $('playhead-label').textContent = showPoint;
  $('oldest-label').textContent = bounds ? timeLabel(bounds.oldest) : '00:00';
  $('edge-label').textContent = bounds ? `${timeLabel(bounds.edge)} · newest` : '00:00';

  if (bounds && !scrubbing) {
    timeline.min = bounds.oldest;
    timeline.max = bounds.edge;
    timeline.value = position ?? bounds.oldest;
  } else if (!bounds) {
    timeline.min = 0;
    timeline.max = 1;
    timeline.value = 0;
  }
  timeline.setAttribute('aria-valuetext', showPoint);
  const progress = (point) => bounds ? 100 * clamp((point - bounds.oldest) / (bounds.edge - bounds.oldest), 0, 1) : 0;
  const track = $('timeline-track');
  track.style.setProperty('--position', `${progress(position ?? bounds?.oldest)}%`);
  $('trim-highlight').hidden = !bounds || duration === null || duration <= 0;
  if (!$('trim-highlight').hidden) {
    track.style.setProperty('--selection-left', `${progress(markIn)}%`);
    track.style.setProperty('--selection-width', `${progress(markOut) - progress(markIn)}%`);
  }

  timeline.disabled = !maySeek;
  $('go-live').disabled = !maySeek || state.stream.status === 'error';
  const liveSync = hls?.liveSyncPosition;
  $('go-live').dataset.tone = maySeek && state.stream.status === 'live' && !state.stream.stalled && !video.paused
    && (Number.isFinite(liveSync) ? video.currentTime >= liveSync - 2 : bounds.edge - current <= 4) ? 'positive' : '';
  $('mark-in').disabled = !maySeek || exporting;
  $('mark-out').disabled = !maySeek || exporting;
  $('clear-marks').disabled = (markIn === null && markOut === null) || exporting;
  $('in-label').textContent = markIn === null ? '—' : timeLabel(markIn, true);
  $('out-label').textContent = markOut === null ? '—' : timeLabel(markOut, true);
  $('clip-duration').textContent = duration !== null && duration > 0 ? timeLabel(duration, true) : '';
  $('last-30').disabled = !bounds || bounds.edge - bounds.oldest < MIN_CLIP || !!operation || exporting;
  $('last-60').disabled = $('last-30').disabled;
  $('preview').disabled = previewEnd === null && (!maySeek || !canExport || exporting);
  $('preview').textContent = previewEnd === null ? 'Preview' : 'Stop preview';
  $('export').disabled = !canExport || !state.stream.id || !!operation || exporting;
  $('export').textContent = exporting ? 'Exporting…' : 'Export MP4';

  let warning = '';
  if (bounds && markIn !== null && markIn < bounds.oldest) {
    warning = 'The in point rolled out of the buffer. Mark a new in point.';
  } else if (duration !== null && (duration < MIN_CLIP || duration > MAX_CLIP)) {
    warning = 'Select between 0.25 seconds and 2 minutes, with the in point before the out point.';
  } else if (state.stream.stalled || state.stream.status === 'stalled' || (bounds && state.stream.status === 'error')) {
    warning = state.stream.error || 'The feed paused. You can still export video from the buffer.';
  }
  setMessage('editor-message', editorNotice || warning, editorNotice ? editorTone : 'warning');
}

function applyState(next) {
  const previousStream = state.stream.id;
  const previousChannel = state.channelId;
  const previousPortal = state.portal;
  const refreshPortal = Object.hasOwn(next, 'portal') && (
    !initialized || offline || operation === 'login' || operation === 'logout' ||
    next.portal?.type !== previousPortal?.type || next.portal?.label !== previousPortal?.label ||
    next.portal?.channels?.length !== previousPortal?.channels?.length
  );
  state = { ...state, ...next };
  initialized = true;
  offline = false;
  if (Object.hasOwn(next, 'vpnNotice')) vpnNotice = next.vpnNotice || '';
  if (refreshPortal) {
    resetGuide({ clearSelection: true });
    channelsById = new Map((state.portal?.channels || []).map((channel) => [channel.id, channel]));
    channelsShown = PAGE_SIZE;
    if (!state.portal) $('channel-search').value = '';
    renderChannels(true);
  } else if (previousChannel !== state.channelId) {
    for (const button of $('channel-list').querySelectorAll('[data-channel-id]')) {
      button.setAttribute('aria-current', String(button.dataset.channelId === state.channelId));
    }
  }
  if (operation === 'tune') pinnedGuideChannel = null;

  if (previousStream !== state.stream.id) {
    markIn = null;
    markOut = null;
    previewEnd = null;
    scrubbing = false;
    editorNotice = '';
    resetPlayer();
  }
  const fragments = state.stream.fragments || [];
  fragmentsBySequence = new Map(fragments.map((fragment) => [Number(fragment.sequence), fragment]));
  fragmentsByName = new Map(fragments.map((fragment) => [fragment.name, fragment]));
  if (state.stream.id && state.stream.id !== mediaId && bufferBounds()) attachPlayer(state.stream.id);
  renderHeader();
  renderStream();
  if (refreshPortal || previousChannel !== state.channelId || operation === 'tune') void refreshGuide();
}

function setOperation(name) {
  operation = name;
  for (const button of $('channel-list').querySelectorAll('[data-channel-id]')) button.disabled = !!operation || exporting;
  renderHeader();
  renderStream();
  renderVpn();
  renderGuide();
}

async function mutate(name, path, body) {
  if (operation || exporting || remoteLocked()) return false;
  const session = remoteSession;
  revision += 1;
  if (name === 'vpn') resetGuide();
  setOperation(name);
  setMessage('workspace-message', '');
  if (name === 'login') setMessage('login-error', '');
  try {
    const response = await post(path, body);
    const next = await response.json();
    if (session !== remoteSession) return false;
    applyState(next);
    return true;
  } catch (error) {
    if (session !== remoteSession) return false;
    if (name === 'vpn') vpnError = error.message;
    else setMessage(name === 'login' ? 'login-error' : 'workspace-message', error.message, 'error');
    return false;
  } finally {
    if (session === remoteSession) {
      revision += 1;
      setOperation(null);
      if (name === 'vpn') void refreshGuide();
    }
  }
}

async function poll() {
  const currentRevision = revision;
  if (!operation && !remoteLocked()) {
    try {
      const response = await request(!initialized || offline ? '/api/state' : '/api/stream');
      const next = await response.json();
      if (currentRevision === revision) applyState(next);
    } catch {
      if (currentRevision === revision) {
        offline = true;
        renderHeader();
      }
    }
  }
  const waitingForStream = ['starting', 'live', 'stalled'].includes(state.stream.status);
  setTimeout(poll, waitingForStream ? 1250 : 3800);
}

function connectedProfile(profile) {
  return profile && String(profile.status).toLowerCase() === 'connected';
}

function selectedProfile() {
  return profiles.find((profile) => profile.name === $('vpn-profile').value);
}

function renderVpn() {
  const active = profiles.find(connectedProfile);
  const profile = selectedProfile();
  const connected = connectedProfile(profile);
  $('vpn-label').textContent = active ? `VPN · ${active.name}` : 'VPN routes';
  $('vpn-open').dataset.tone = active ? 'positive' : '';
  $('vpn-open').title = active ? `Connected VPN profile: ${active.name}` : 'Choose a Windows VPN profile';
  $('vpn-controls').hidden = !profiles.length;
  $('vpn-profile').disabled = vpnLoading || !!operation;
  $('vpn-refresh').disabled = vpnLoading || !!operation;
  $('vpn-change').disabled = vpnLoading || !!operation || exporting || !profile;
  $('vpn-change').textContent = operation === 'vpn' ? 'Updating route…' : connected ? 'Disconnect VPN' : 'Connect VPN';
  const text = profile?.splitTunnel === true
    ? 'Split tunneling is on. The stream may use your regular connection.'
    : connected ? 'Windows reports that this profile is connected.' : 'Using a different route can change stream performance.';
  setMessage('vpn-profile-info', profile ? text : '', profile?.splitTunnel === true ? 'warning' : '');
  if (vpnError) {
    setMessage('vpn-message', vpnError, 'error');
  } else if (vpnLoading) {
    setMessage('vpn-message', 'Reading Windows VPN profiles…');
  } else if (state.vpnAvailable === false) {
    setMessage('vpn-message', 'This app manages VPN profiles through Windows.');
  } else if (!profiles.length) {
    setMessage('vpn-message', 'Add a profile in Windows Settings under Network & internet → VPN. Name it for the region, such as United Kingdom.');
  } else {
    setMessage('vpn-message', vpnNotice || (bufferBounds() ? 'Changing the route restarts the channel with a fresh buffer.' : ''));
  }
}

async function loadVpn() {
  if (remoteLocked()) return;
  const token = ++vpnRevision;
  vpnLoading = true;
  renderVpn();
  try {
    const response = await request('/api/vpn');
    const next = await response.json();
    if (token !== vpnRevision) return;
    const select = $('vpn-profile');
    const previous = select.value;
    profiles = next.profiles || [];
    select.replaceChildren(...profiles.map((profile) => new Option(`${profile.name}${connectedProfile(profile) ? ' (connected)' : ''}`, profile.name)));
    const preferred = profiles.find((profile) => profile.name === previous) || profiles.find(connectedProfile);
    if (preferred) select.value = preferred.name;
  } catch (error) {
    if (token === vpnRevision && !vpnError) vpnError = error.message;
  } finally {
    if (token === vpnRevision) {
      vpnLoading = false;
      renderVpn();
    }
  }
}

function mark(which) {
  const current = dvrPosition();
  if (current === null) return;
  if (which === 'in') markIn = current;
  else markOut = current;
  editorNotice = '';
  renderEditor();
}

function markRecent(seconds) {
  const bounds = bufferBounds();
  if (!bounds) return;
  markIn = Math.max(bounds.oldest, bounds.edge - seconds);
  markOut = bounds.edge;
  editorNotice = '';
  renderEditor();
}

function stopPreview() {
  if (previewEnd === null) return;
  previewEnd = null;
  video.pause();
  renderEditor();
}

function downloadName(response) {
  const disposition = response.headers.get('Content-Disposition') || '';
  const safeName = (name) => name.split(/[\\/]/).at(-1).replace(/[\u0000-\u001f]/g, '');
  const utf8 = disposition.match(/filename\*=UTF-8''([^;]+)/i);
  if (utf8) {
    try { return safeName(decodeURIComponent(utf8[1])); } catch { /* Use the plain filename. */ }
  }
  const filename = disposition.match(/filename="([^"\r\n]+)"/i);
  return filename ? safeName(filename[1]) : 'live-clip.mp4';
}

async function exportClip() {
  if ($('export').disabled || remoteLocked()) return;
  const session = remoteSession;
  exporting = true;
  editorNotice = 'Preparing the MP4…';
  editorTone = '';
  setOperation(null);
  try {
    const response = await post('/api/clip', { id: state.stream.id, start: markIn, end: markOut });
    const clip = await response.blob();
    if (session !== remoteSession) return;
    const url = URL.createObjectURL(clip);
    downloadLinks.add(url);
    const anchor = document.createElement('a');
    anchor.href = url;
    anchor.download = downloadName(response);
    document.body.append(anchor);
    anchor.click();
    anchor.remove();
    setTimeout(() => {
      URL.revokeObjectURL(url);
      downloadLinks.delete(url);
    }, 30_000);
    editorNotice = 'MP4 sent to your browser’s downloads.';
    editorTone = 'positive';
  } catch (error) {
    if (session !== remoteSession) return;
    editorNotice = error.message;
    editorTone = 'error';
  } finally {
    if (session === remoteSession) {
      exporting = false;
      setOperation(null);
    }
  }
}

$('backend-form').addEventListener('submit', connectBackend);
$('backend-lock').addEventListener('click', () => lockRemote());
window.addEventListener('pagehide', () => {
  if (remoteSession) lockRemote('', { focus: false });
  else if (onPages) $('backend-key').value = '';
});
$('login-form').addEventListener('submit', async (event) => {
  event.preventDefault();
  if (operation) return;
  const fields = Object.fromEntries(new FormData(event.currentTarget));
  const { type, url, username, password, format } = fields;
  const credentials = type === 'stalker' ? stalkerCredentials(fields) : { username, password, ...(format && { format }) };
  if (await mutate('login', '/api/login', { type, url: url.trim(), ...credentials })) {
    for (const id of ['username', 'password', 'mac', 'stalker-label', 'stalker-serial-number', 'stalker-device-id', 'stalker-device-id-2', 'stalker-username', 'stalker-password']) {
      $(id).value = '';
    }
    $('channel-search').focus();
  }
});
$('login-form').addEventListener('change', (event) => {
  if (event.target.name !== 'type') return;
  updateLoginForm();
  setMessage('login-error', '');
});
$('logout').addEventListener('click', async () => {
  if (await mutate('logout', '/api/logout', {})) $('portal-url').focus();
});
$('channel-list').addEventListener('click', (event) => {
  const guideButton = event.target.closest('[data-guide-channel]');
  if (guideButton) {
    const channelId = guideButton.dataset.guideChannel;
    pinnedGuideChannel = channelId === state.channelId ? null : channelId;
    void refreshGuide();
    $('guide-title').focus({ preventScroll: true });
    $('guide-panel').scrollIntoView({ block: 'nearest' });
    return;
  }
  const button = event.target.closest('[data-channel-id]');
  if (!button) return;
  const channelId = button.dataset.channelId;
  if (channelId !== state.channelId || state.stream.status === 'error' || state.stream.status === 'idle') {
    void mutate('tune', '/api/tune', { channelId });
  }
});
for (const [id, eventName] of [['channel-search', 'input'], ['category', 'change']]) {
  $(id).addEventListener(eventName, () => {
    channelsShown = PAGE_SIZE;
    renderChannels();
  });
}
$('channel-more').addEventListener('click', () => {
  const firstNewIndex = channelsShown;
  channelsShown += PAGE_SIZE;
  renderChannels();
  $('channel-list').querySelectorAll('[data-channel-id]')[firstNewIndex]?.focus();
});
$('guide-follow').addEventListener('click', () => {
  pinnedGuideChannel = null;
  void refreshGuide();
  $('guide-title').focus({ preventScroll: true });
});
$('guide-refresh').addEventListener('click', () => { void refreshGuide(true); });
document.addEventListener('visibilitychange', () => {
  if (!document.hidden) void refreshGuide();
});
setInterval(() => { if (!document.hidden && state.portal) void refreshGuide(); }, 15_000);
$('stop').addEventListener('click', () => { void mutate('stop', '/api/stop', {}); });
$('player-retry').addEventListener('click', () => {
  if (playerError && state.stream.id && bufferBounds()) {
    attachPlayer(state.stream.id);
    renderStream();
  } else if (state.channelId) {
    void mutate('tune', '/api/tune', { channelId: state.channelId });
  }
});

video.addEventListener('error', () => {
  if (!mediaId || hls) return;
  playerError = 'The browser could not play the live preview.';
  renderStream();
});
for (const event of ['play', 'pause', 'volumechange', 'loadedmetadata']) {
  video.addEventListener(event, () => { renderPlaybackControls(); renderEditor(); });
}
video.addEventListener('timeupdate', () => {
  if (previewEnd !== null && (dvrPosition() ?? -1) >= previewEnd - 0.06) stopPreview();
  renderEditor();
});
$('play').addEventListener('click', () => {
  if (video.paused) video.play().catch(() => {});
  else if (previewEnd !== null) stopPreview();
  else video.pause();
});
$('mute').addEventListener('click', () => { video.muted = !video.muted; });
$('fullscreen').addEventListener('click', () => {
  const promise = document.fullscreenElement ? document.exitFullscreen() : video.closest('.player-panel').requestFullscreen();
  promise.catch(() => {});
});
$('go-live').addEventListener('click', () => {
  stopPreview();
  if (Number.isFinite(hls?.liveSyncPosition)) video.currentTime = hls.liveSyncPosition;
  else seekTo((bufferBounds()?.edge ?? 0) - 2);
  video.play().catch(() => {});
});
timeline.addEventListener('input', () => {
  scrubbing = true;
  renderEditor();
});
timeline.addEventListener('change', () => {
  const target = Number(timeline.value);
  scrubbing = false;
  stopPreview();
  seekTo(target);
  renderEditor();
});
for (const event of ['blur', 'pointercancel']) {
  timeline.addEventListener(event, () => {
    scrubbing = false;
    renderEditor();
  });
}
$('mark-in').addEventListener('click', () => mark('in'));
$('mark-out').addEventListener('click', () => mark('out'));
$('last-30').addEventListener('click', () => markRecent(30));
$('last-60').addEventListener('click', () => markRecent(60));
$('clear-marks').addEventListener('click', () => {
  stopPreview();
  markIn = null;
  markOut = null;
  editorNotice = '';
  renderEditor();
});
$('preview').addEventListener('click', () => {
  if (previewEnd !== null) {
    stopPreview();
  } else if (seekTo(markIn)) {
    previewEnd = markOut;
    video.play().catch(() => { stopPreview(); });
    renderEditor();
  }
});
$('export').addEventListener('click', () => { void exportClip(); });

$('vpn-open').addEventListener('click', () => {
  dialog.showModal();
  vpnError = '';
  void loadVpn();
});
$('vpn-refresh').addEventListener('click', () => {
  vpnError = '';
  void loadVpn();
});
$('vpn-profile').addEventListener('change', () => {
  vpnError = '';
  vpnNotice = '';
  renderVpn();
});
$('vpn-change').addEventListener('click', async () => {
  const profile = selectedProfile();
  if (!profile || operation || exporting) return;
  vpnError = '';
  vpnNotice = '';
  const session = remoteSession;
  const action = connectedProfile(profile) ? 'disconnect' : 'connect';
  await mutate('vpn', '/api/vpn', { action, name: profile.name });
  if (session === remoteSession) await loadVpn();
});

updateLoginForm();
renderBackend();
renderStream();
void poll();
void loadVpn();
