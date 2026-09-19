/**
 * Diablo IV Interactive Map Engine v2.5 (English Edition)
 * Sanctuary Complete Tracker with Bulletproof Multi-Layer Persistence
 * Features: Offline-First, Dual-Layer Storage (localStorage + Server Disk),
 * Zero-Counter-Reset Architecture, Region Isolation, Mass Actions,
 * Aspect Search Drawer, Checklist Inspection, Route Tool, and Web Audio Chimes.
 */

(function () {
  "use strict";

  // Configuration & Constants
  const REGION_BOUNDS = {
    "Fractured Peaks": { center: [0.7157, -0.6210], bounds: [[0.6637, -0.6916], [0.7678, -0.5504]] },
    "Scosglen": { center: [0.8213, -0.6627], bounds: [[0.7503, -0.7595], [0.8923, -0.5660]] },
    "Dry Steppes": { center: [0.7312, -0.7637], bounds: [[0.6618, -0.8423], [0.8006, -0.6851]] },
    "Kehjistan": { center: [0.6309, -0.7828], bounds: [[0.5653, -0.8799], [0.6966, -0.6857]] },
    "Hawezar": { center: [0.6098, -0.6467], bounds: [[0.5434, -0.7392], [0.6762, -0.5542]] },
    "Nahantu": { center: [0.5091, -0.8130], bounds: [[0.4245, -0.9164], [0.5938, -0.7097]] }
  };

  const SANCTUARY_TILE_URL = "https://tiles.mapgenie.io/games/diablo-4/sanctuary/default-v5/{z}/{x}/{y}.jpg";

  const ICONS_CONFIG = {
    "Altar of Lilith": {
      default: "assets/icons/altar_of_lilith.png",
      active: "assets/icons/altar_of_lilith_active.png",
      size: [24, 24]
    },
    "Tenet of Akarat": {
      default: "assets/icons/tenet_of_akarat.png",
      active: "assets/icons/tenet_of_akarat_active.png",
      size: [24, 24]
    },
    "Waygate": {
      default: "assets/icons/waygate.png",
      active: "assets/icons/waygate_active.png",
      size: [24, 24]
    },
    "Dungeon": {
      default: "assets/icons/dungeon.png",
      active: "assets/icons/dungeon_active.png",
      size: [24, 24]
    },
    "Stronghold": {
      default: "assets/icons/stronghold.png",
      active: "assets/icons/stronghold_active.png",
      size: [26, 26]
    },
    "World Boss": {
      default: "assets/icons/boss.png",
      active: "assets/icons/boss.png",
      size: [28, 28]
    },
    "Boss Lair": {
      default: "assets/icons/dungeon_boss.png",
      active: "assets/icons/dungeon_boss.png",
      size: [26, 26]
    }
  };

  // Safe Storage & Sanitization Helpers
  function safeStorageGet(key, defaultVal = null) {
    try {
      if (typeof window !== "undefined" && window.localStorage) {
        const v = window.localStorage.getItem(key);
        return v !== null ? v : defaultVal;
      }
    } catch (e) {}
    return defaultVal;
  }

  function safeStorageSet(key, value) {
    try {
      if (typeof window !== "undefined" && window.localStorage) {
        window.localStorage.setItem(key, value);
      }
    } catch (e) {
      console.warn("Storage write failed or quota exceeded:", e);
    }
  }

  function escapeHTML(str) {
    if (!str) return "";
    return String(str)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;")
      .replace(/'/g, "&#039;");
  }

  // State
  const currentRealm = "Eternal";
  let map = null;
  let baseTileLayer = null;
  let trackedMarkers = {}; // Normalized: String(id) -> true
  let customPins = [];
  let routePoints = [];
  let routePolyline = null;
  let routeMarkers = [];

  let isMeasuring = false;
  let isPinMode = false;
  let isDraggingMap = false;
  let dragEndTimeout = null;
  let globalTooltipEl = null;
  let activeTooltipMarker = null;
  let tooltipHideTimeout = null;
  let hideCompleted = false;
  let searchTerm = "";
  let activeClass = null;
  let isolatedRegion = null;
  let soundEnabled = safeStorageGet("d4_sound_enabled", "true") !== "false";
  let saveDebounceTimer = null;
  let audioCtx = null;

  // Active category filters (default all true)
  const activeFilters = {
    "Altar of Lilith": true,
    "Tenet of Akarat": true,
    "Waygate": true,
    "Dungeon": true,
    "Stronghold": true,
    "World Boss": true,
    "Boss Lair": true
  };

  // Map markers cache: id -> { data, markerInstance }
  const markersCache = new Map();
  const customPinsGroup = L.layerGroup();
  const markersLayerGroup = L.layerGroup();

  // Subregions & Major Regions layers
  let subregionsEnabled = safeStorageGet("d4_subregions_enabled", "true") !== "false";
  const mainRegionsLayerGroup = L.layerGroup();
  const subregionsLayerGroup = L.layerGroup();
  let subregionHudEl = null;
  let subregionCursorEl = null;
  let hoveredSubregionLayer = null;

  // Web Audio Synth for collection feedback
  function playCollectSound() {
    if (!soundEnabled) return;
    try {
      if (!audioCtx) {
        audioCtx = new (window.AudioContext || window.webkitAudioContext)();
      }
      if (audioCtx.state === "suspended") {
        audioCtx.resume();
      }
      const now = audioCtx.currentTime;
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();

      osc.type = "sine";
      osc.frequency.setValueAtTime(587.33, now); // D5
      osc.frequency.exponentialRampToValueAtTime(880.0, now + 0.08); // A5
      osc.frequency.exponentialRampToValueAtTime(1174.66, now + 0.16); // D6

      gain.gain.setValueAtTime(0.12, now);
      gain.gain.exponentialRampToValueAtTime(0.001, now + 0.35);

      osc.connect(gain);
      gain.connect(audioCtx.destination);

      osc.start(now);
      osc.stop(now + 0.35);
    } catch (e) {
      // AudioContext not allowed before user gesture
    }
  }

  // Pure Parity Helpers for IDs
  function isMarkerTracked(id) {
    if (id === undefined || id === null) return false;
    return Boolean(trackedMarkers[String(id)] || trackedMarkers[id]);
  }

  function setMarkerTracked(id, state) {
    const sId = String(id);
    if (state) {
      trackedMarkers[sId] = true;
    } else {
      delete trackedMarkers[sId];
      delete trackedMarkers[id];
    }
  }

  // Storage Keys & Multi-Layer Persistence
  function getStorageKey() {
    return "d4_trackedMarkers";
  }

  // Request persistent storage so browser never evicts saved data
  if (typeof navigator !== "undefined" && navigator.storage && navigator.storage.persist) {
    navigator.storage.persist().catch(function () {});
  }

  function updateSaveIndicator() {
    // Silent persistence: zero UI clutter or AI status badges
  }

  function loadTrackedState() {
    const key = getStorageKey();
    let loaded = false;
    const stored = safeStorageGet(key);

    if (stored) {
      try {
        trackedMarkers = JSON.parse(stored);
        loaded = true;
      } catch (e) {
        trackedMarkers = {};
      }
    }

    // Secondary local fallback: check backup key
    if (!loaded || Object.keys(trackedMarkers).length === 0) {
      const backup = safeStorageGet("d4_trackedMarkers_backup");
      const legacy = safeStorageGet("trackedMarkers");
      const candidate = backup || legacy;
      if (candidate) {
        try {
          const parsed = JSON.parse(candidate);
          if (parsed && typeof parsed === "object") {
            trackedMarkers = parsed;
            loaded = true;
          }
        } catch (e) {}
      }
    }

    // Enforce string keys for total consistency
    const normalized = {};
    for (const [k, v] of Object.entries(trackedMarkers)) {
      if (v) normalized[String(k)] = true;
    }
    trackedMarkers = normalized;

    // Dual-layer: Try reading server disk backup in background if served via HTTP on local link server
    const isLocalServer = window.location.hostname === "localhost" || window.location.hostname === "127.0.0.1";
    if (isLocalServer) {
      fetch("/d4map/user_progress.json?t=" + Date.now())
        .then((res) => {
          if (!res.ok) throw new Error("HTTP error");
          return res.json();
        })
        .then((diskData) => {
          if (diskData) {
            let merged = 0;
            if (diskData.trackedMarkers && typeof diskData.trackedMarkers === "object") {
              for (const [k, v] of Object.entries(diskData.trackedMarkers)) {
                const strK = String(k);
                if (v && !trackedMarkers[strK]) {
                  trackedMarkers[strK] = true;
                  merged++;
                }
              }
            }

            // Restore custom pins from disk if local storage was cleared
            if (Array.isArray(diskData.customPins) && customPins.length === 0 && diskData.customPins.length > 0) {
              customPins = diskData.customPins;
              safeStorageSet("d4_custom_pins", JSON.stringify(customPins));
              renderCustomPins();
            }

            if (merged > 0) {
              safeStorageSet(key, JSON.stringify(trackedMarkers));
              renderMarkers();
              updateProgressCounters();
              updateAllOpenDrawers();
              showToast(`Synced: ${merged} markers restored from disk.`);
            }
            updateSaveIndicator("saved");
          }
        })
        .catch(() => {
          updateSaveIndicator("local_only");
        });
    } else {
      updateSaveIndicator("local_only");
    }
  }

  function saveTrackedState() {
    const key = getStorageKey();
    const serialized = JSON.stringify(trackedMarkers);

    // 1. Primary localStorage key
    safeStorageSet(key, serialized);

    // 2. Permanent redundancy key
    safeStorageSet("d4_trackedMarkers_backup", serialized);

    // 3. d4builds.gg compatibility key
    safeStorageSet("trackedMarkers", serialized);

    // Visual indicator: Saving
    updateSaveIndicator("saving");

    // 4. Server Disk Persistence (POST /d4map/save_progress)
    if (saveDebounceTimer) clearTimeout(saveDebounceTimer);
    saveDebounceTimer = setTimeout(() => {
      saveToDisk();
    }, 350);
  }

  function saveToDisk() {
    const isLocalServer = window.location.hostname === "localhost" || window.location.hostname === "127.0.0.1";
    if (isLocalServer) {
      const payload = {
        realm: currentRealm,
        savedAt: new Date().toISOString(),
        totalTracked: Object.keys(trackedMarkers).length,
        trackedMarkers: trackedMarkers,
        customPins: customPins
      };

      fetch("/d4map/save_progress", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload)
      })
        .then((res) => {
          if (res.ok) {
            updateSaveIndicator("saved");
          } else {
            updateSaveIndicator("local_only");
          }
        })
        .catch(() => {
          updateSaveIndicator("local_only");
        });
    } else {
      updateSaveIndicator("local_only");
    }
  }

  function loadCustomPins() {
    const stored = safeStorageGet("d4_custom_pins");
    if (stored) {
      try {
        customPins = JSON.parse(stored);
      } catch (e) {
        customPins = [];
      }
    }
  }

  function saveCustomPins() {
    safeStorageSet("d4_custom_pins", JSON.stringify(customPins));
    saveToDisk();
  }

  // Initialize
  function init() {
    loadTrackedState();
    loadCustomPins();
    setupMap();
    initGlobalTooltip();
    initSubregions();
    setupUI();
    renderMarkers();
    updateProgressCounters();
  }

  // Single Global Floating Tooltip Controller (100% immune to multi-tooltip stacking & pan-stick bugs)
  function initGlobalTooltip() {
    if (globalTooltipEl) return;
    globalTooltipEl = document.createElement("div");
    globalTooltipEl.id = "d4GlobalTooltip";
    globalTooltipEl.className = "d4-global-tooltip";
    globalTooltipEl.style.display = "none";
    const mapEl = document.getElementById("map");
    if (mapEl) {
      mapEl.appendChild(globalTooltipEl);
    }
  }

  function showGlobalTooltip(marker, data) {
    if (isDraggingMap || !globalTooltipEl || !map) return;
    hideSubregionCursorBadge();
    if (tooltipHideTimeout) {
      clearTimeout(tooltipHideTimeout);
      tooltipHideTimeout = null;
    }

    activeTooltipMarker = marker;
    globalTooltipEl.innerHTML = buildTooltipHTML(data);
    updateGlobalTooltipPosition(marker);
    globalTooltipEl.style.display = "block";
  }

  function updateGlobalTooltipPosition(marker) {
    if (!globalTooltipEl || !map || !marker) return;
    const pt = map.latLngToContainerPoint(marker.getLatLng());
    globalTooltipEl.style.left = pt.x + "px";
    globalTooltipEl.style.top = pt.y + "px";

    if (pt.y < 240) {
      globalTooltipEl.classList.add("tooltip-bottom");
    } else {
      globalTooltipEl.classList.remove("tooltip-bottom");
    }
  }

  function hideGlobalTooltip() {
    if (tooltipHideTimeout) {
      clearTimeout(tooltipHideTimeout);
      tooltipHideTimeout = null;
    }
    if (globalTooltipEl) {
      globalTooltipEl.style.display = "none";
    }
    activeTooltipMarker = null;
  }

  function updateGlobalTooltipIfActive(id) {
    if (activeTooltipMarker && String(activeTooltipMarker._d4Id) === String(id)) {
      const entry = markersCache.get(String(id));
      if (entry && globalTooltipEl) {
        globalTooltipEl.innerHTML = buildTooltipHTML(entry.data);
      }
    }
  }

  function showGlobalTooltipForMarker(id, durationMs = 3500) {
    const entry = markersCache.get(String(id));
    if (!entry) return;
    showGlobalTooltip(entry.marker, entry.data);
    if (durationMs > 0) {
      tooltipHideTimeout = setTimeout(() => {
        hideGlobalTooltip();
      }, durationMs);
    }
  }

  // --- Subregion & Major Zone Controllers ---
  let badgeRaf = null;

  function initSubregionHUD() {
    if (subregionHudEl) return;
    subregionHudEl = document.createElement("div");
    subregionHudEl.id = "d4SubregionHud";
    subregionHudEl.className = "d4-subregion-hud";
    subregionHudEl.style.display = "none";
    subregionHudEl.innerHTML = `
      <span class="d4-subregion-hud-icon">🛡</span>
      <div class="d4-subregion-hud-body">
        <div class="d4-subregion-hud-title" id="d4SubregionHudTitle">Sanctuary</div>
        <div class="d4-subregion-hud-zone" id="d4SubregionHudZone">Continent</div>
      </div>
    `;
    const mapEl = document.getElementById("map");
    if (mapEl) {
      mapEl.appendChild(subregionHudEl);
    }
  }

  function initSubregionCursorBadge() {
    if (subregionCursorEl) return;
    subregionCursorEl = document.createElement("div");
    subregionCursorEl.id = "d4SubregionCursorBadge";
    subregionCursorEl.className = "d4-subregion-cursor-badge";
    subregionCursorEl.style.display = "none";
    const mapEl = document.getElementById("map");
    if (mapEl) {
      mapEl.appendChild(subregionCursorEl);
    }
  }

  function showSubregionHud(props) {
    if (!subregionHudEl || isDraggingMap) return;
    const titleEl = document.getElementById("d4SubregionHudTitle");
    const zoneEl = document.getElementById("d4SubregionHudZone");
    if (titleEl) titleEl.textContent = props.title;
    if (zoneEl) zoneEl.textContent = props.parent_title || "Sanctuary";
    subregionHudEl.style.display = "flex";
  }

  function restoreSubregionStyle(layer) {
    if (!layer) return;
    if (isolatedRegion && layer._subregionData) {
      const isTarget = (layer._subregionData.parent_title === isolatedRegion);
      if (isTarget) {
        layer.setStyle({
          color: "#c9a050",
          weight: 1.8,
          opacity: 0.7,
          fillColor: "#988f7b",
          fillOpacity: 0.05
        });
      } else {
        layer.setStyle({
          color: "#302b23",
          weight: 1.0,
          opacity: 0.15,
          fillColor: "#988f7b",
          fillOpacity: 0.0
        });
      }
    } else if (layer._defaultStyle) {
      layer.setStyle(layer._defaultStyle);
    }
  }

  function applySubregionHover(layer, feature, e) {
    if (!subregionsEnabled || isDraggingMap || (map && map.dragging && map.dragging.moving())) return;
    // When a region is isolated, only allow hover on subregions inside that region
    if (isolatedRegion && feature && feature.properties && feature.properties.parent_title !== isolatedRegion) {
      return;
    }
    if (hoveredSubregionLayer !== layer) {
      if (hoveredSubregionLayer) {
        restoreSubregionStyle(hoveredSubregionLayer);
      }
      hoveredSubregionLayer = layer;
      layer.setStyle(layer._hoverStyle);
      if (layer.bringToFront) {
        layer.bringToFront();
      }
      showSubregionHud(feature.properties);
    }
    showSubregionCursorBadge(e, feature.properties);
  }

  function showSubregionCursorBadge(e, props) {
    if (!subregionCursorEl || isDraggingMap || activeTooltipMarker) return;
    subregionCursorEl.innerHTML = `<b>${escapeHTML(props.title)}</b>${props.parent_title ? ` <span class="badge-subzone">• ${escapeHTML(props.parent_title)}</span>` : ""}`;
    updateSubregionCursorBadge(e);
    subregionCursorEl.style.display = "block";
  }

  function updateSubregionCursorBadge(e) {
    if (!subregionCursorEl || isDraggingMap || activeTooltipMarker) return;
    // Fast path: use e.containerPoint directly from Leaflet (0 layout reflow!)
    const pt = e && e.containerPoint ? e.containerPoint : (e && e.latlng && map ? map.latLngToContainerPoint(e.latlng) : null);
    if (!pt) return;
    const x = Math.round(pt.x + 14);
    const y = Math.round(pt.y + 14);
    if (badgeRaf) cancelAnimationFrame(badgeRaf);
    badgeRaf = requestAnimationFrame(() => {
      if (subregionCursorEl) {
        subregionCursorEl.style.transform = `translate3d(${x}px, ${y}px, 0)`;
      }
    });
  }

  function hideSubregionCursorBadge() {
    if (badgeRaf) {
      cancelAnimationFrame(badgeRaf);
      badgeRaf = null;
    }
    if (subregionCursorEl) {
      subregionCursorEl.style.display = "none";
    }
  }

  function hideSubregionHover() {
    if (hoveredSubregionLayer && hoveredSubregionLayer._defaultStyle) {
      hoveredSubregionLayer.setStyle(hoveredSubregionLayer._defaultStyle);
      hoveredSubregionLayer = null;
    }
    if (subregionHudEl) {
      subregionHudEl.style.display = "none";
    }
    hideSubregionCursorBadge();
  }

  function initSubregions() {
    initSubregionHUD();
    initSubregionCursorBadge();

    if (!window.D4_SUBREGIONS_GEOJSON) return;

    // 1. Major Zone Outer Boundaries (Scosglen, Fractured Peaks, Dry Steppes, etc.)
    if (window.D4_REGIONS_GEOJSON) {
      L.geoJSON(window.D4_REGIONS_GEOJSON, {
        pane: "regionsPane",
        interactive: false,
        style: {
          color: "#4e4537",
          weight: 2.0,
          opacity: 0.6,
          fill: false,
          dashArray: "4, 6"
        }
      }).addTo(mainRegionsLayerGroup);
    }

    // 2. Subregions (Highland Wilds, Deep Forest, The Emerald Chase, etc.)
    const defaultSubregionStyle = {
      color: "#444035",
      weight: 1.5,
      opacity: 0.35,
      fillColor: "#988f7b",
      fillOpacity: 0.0,
      lineCap: "round",
      lineJoin: "round",
      pane: "subregionsPane"
    };

    const hoverSubregionStyle = {
      color: "#c9a050", // Diablo Gold
      weight: 2.5,
      opacity: 1.0,
      fillColor: "#988f7b",
      fillOpacity: 0.16,
      lineCap: "round",
      lineJoin: "round"
    };

    L.geoJSON(window.D4_SUBREGIONS_GEOJSON, {
      pane: "subregionsPane",
      style: defaultSubregionStyle,
      onEachFeature: function (feature, layer) {
        layer._defaultStyle = defaultSubregionStyle;
        layer._hoverStyle = hoverSubregionStyle;
        layer._subregionData = feature.properties;

        layer.on("mouseover", function (e) {
          applySubregionHover(layer, feature, e);
        });

        layer.on("mousemove", function (e) {
          applySubregionHover(layer, feature, e);
        });

        layer.on("mouseout", function () {
          restoreSubregionStyle(layer);
          if (hoveredSubregionLayer === layer) {
            hoveredSubregionLayer = null;
          }
          hideSubregionHover();
        });

        layer.on("click", function (e) {
          if (isDraggingMap || isPinMode || isMeasuring) return;
          // Maintain active hover delimiter on click without jarring flyToBounds jump
          applySubregionHover(layer, feature, e);
        });
      }
    }).addTo(subregionsLayerGroup);

    if (!subregionsEnabled) {
      if (map.hasLayer(mainRegionsLayerGroup)) map.removeLayer(mainRegionsLayerGroup);
      if (map.hasLayer(subregionsLayerGroup)) map.removeLayer(subregionsLayerGroup);
    }
  }

  // Setup Leaflet Map (Sanctuary Only, Keyboard Navigation Disabled to Prevent Tab Recenter)
  function setupMap() {
    map = L.map("map", {
      center: [0.68, -0.72],
      zoom: 11,
      minZoom: 9,
      maxZoom: 16,
      maxBounds: [[0.20, -1.45], [1.35, -0.35]],
      maxBoundsViscosity: 0.6,
      zoomControl: false,
      attributionControl: false,
      keyboard: false
    });

    baseTileLayer = L.tileLayer(SANCTUARY_TILE_URL, {
      noWrap: true,
      maxZoom: 16,
      maxNativeZoom: 16,
      minZoom: 9,
      updateWhenIdle: true,
      updateInterval: 120,
      keepBuffer: 2
    }).addTo(map);

    // Custom panes for regions and subregions (below markerPane at zIndex 600)
    map.createPane("regionsPane");
    map.getPane("regionsPane").style.zIndex = "340";

    map.createPane("subregionsPane");
    map.getPane("subregionsPane").style.zIndex = "350";

    mainRegionsLayerGroup.addTo(map);
    subregionsLayerGroup.addTo(map);

    markersLayerGroup.addTo(map);
    customPinsGroup.addTo(map);

    function handleMapDragStart() {
      isDraggingMap = true;
      hideGlobalTooltip();
      hideSubregionHover();
      if (dragEndTimeout) {
        clearTimeout(dragEndTimeout);
        dragEndTimeout = null;
      }
      const container = map.getContainer();
      if (container) {
        container.classList.add("map-is-dragging");
      }
    }

    function handleMapDragEnd() {
      hideGlobalTooltip();
      if (dragEndTimeout) clearTimeout(dragEndTimeout);
      dragEndTimeout = setTimeout(() => {
        isDraggingMap = false;
        const container = map ? map.getContainer() : null;
        if (container) {
          container.classList.remove("map-is-dragging");
        }
      }, 80);
    }

    map.on("dragstart", handleMapDragStart);
    map.on("movestart", function () {
      if (map.dragging && map.dragging.moving()) {
        handleMapDragStart();
      } else {
        hideGlobalTooltip();
      }
    });

    map.on("dragend", handleMapDragEnd);
    map.on("moveend", function () {
      if (isDraggingMap) {
        handleMapDragEnd();
      } else {
        hideGlobalTooltip();
      }
    });

    map.on("move", function () {
      if (isDraggingMap) {
        hideGlobalTooltip();
      } else if (activeTooltipMarker) {
        updateGlobalTooltipPosition(activeTooltipMarker);
      }
    });

    map.on("zoomstart", function () {
      hideGlobalTooltip();
      handleMapDragStart();
    });
    map.on("zoomend", handleMapDragEnd);

    const mapContainer = map.getContainer();
    if (mapContainer) {
      mapContainer.addEventListener("mousedown", () => {
        hideGlobalTooltip();
      }, { passive: true });
      mapContainer.addEventListener("touchstart", () => {
        hideGlobalTooltip();
      }, { passive: true });
    }

    map.on("click", function (e) {
      hideGlobalTooltip();
      if (isPinMode) {
        handleCreatePin(e.latlng);
      } else if (isMeasuring) {
        handleAddRoutePoint(e.latlng);
      }
    });
  }

  // Create Marker Icon
  function createMarkerIcon(type, isCompleted) {
    const conf = ICONS_CONFIG[type] || ICONS_CONFIG["Dungeon"];
    const iconUrl = isCompleted && conf.active ? conf.active : conf.default;

    return L.divIcon({
      className: "d4-marker-wrapper",
      html: `
        <div class="d4-marker ${isCompleted ? "completed" : ""}">
          <img src="${iconUrl}" style="width:${conf.size[0]}px; height:${conf.size[1]}px; object-fit:contain;" />
          ${isCompleted ? '<div class="d4-marker-completed-badge">✓</div>' : ""}
        </div>
      `,
      iconSize: conf.size,
      iconAnchor: [conf.size[0] / 2, conf.size[1] / 2],
      popupAnchor: [0, -conf.size[1] / 2]
    });
  }

  // Format aspect descriptions with highlighted bracket values
  function formatAspectDescription(desc) {
    if (!desc) return "";
    return escapeHTML(desc).replace(/(\[[^\]]+\])/g, "<span>$1</span>");
  }

  // Build Tooltip HTML
  function buildTooltipHTML(m) {
    const isCompleted = isMarkerTracked(m.id);
    let extraHTML = "";

    if (m.special && m.type === "Altar of Lilith") {
      extraHTML += `<div class="map-tooltip-paragon">✨ Awards Renown / Stat Bonus</div>`;
    }
    if (m.extra) {
      extraHTML += `<div class="map-tooltip-subtitle">${escapeHTML(m.extra)}</div>`;
    }

    let aspectHTML = "";
    if (m.aspect) {
      const descHTML = formatAspectDescription(m.aspect.description);
      aspectHTML = `
        <div class="map-tooltip-aspect">
          <div class="map-tooltip-aspect-header">
            <img class="map-tooltip-aspect-icon" src="${m.aspect.icon}" alt="${escapeHTML(m.aspect.type || "Aspect")}" />
            <div>
              <div class="map-tooltip-aspect-name">${escapeHTML(m.aspect.name)}</div>
              <div class="map-tooltip-aspect-extra">Codex of Power • <b>${escapeHTML(m.aspect.class || m.class || "All Classes")}</b></div>
            </div>
          </div>
          <div class="map-tooltip-aspect-description">${descHTML}</div>
        </div>
      `;
    }

    return `
      <div class="map-tooltip">
        <div class="map-tooltip-title">${escapeHTML(m.name)}</div>
        <div class="map-tooltip-subtitle">${escapeHTML(m.zone)} • ${escapeHTML(m.type)}</div>
        ${extraHTML}
        ${aspectHTML}
        <div class="map-tooltip-footer">
          <div class="map-tooltip-status ${isCompleted ? "completed" : "not-completed"}">
            <span class="status-bullet">${isCompleted ? "✓" : "○"}</span>
            <span class="status-label">${isCompleted ? "Completed" : "Incomplete"}</span>
          </div>
          <div class="map-tooltip-hint">Click icon to toggle</div>
        </div>
      </div>
    `;
  }

  // Render all markers onto the map
  function renderMarkers() {
    markersLayerGroup.clearLayers();
    markersCache.clear();

    const data = window.D4_MARKERS || [];

    data.forEach((m) => {
      if (m.type === "ZoneName") return;

      const isCompleted = isMarkerTracked(m.id);
      const icon = createMarkerIcon(m.type, isCompleted);
      const marker = L.marker(m.coords, { icon: icon, keyboard: false });

      marker._d4Id = m.id;

      marker.on("mouseover", function () {
        if (!isDraggingMap && !(map && map.dragging && map.dragging.moving())) {
          showGlobalTooltip(marker, m);
        }
      });

      marker.on("mouseout", function () {
        hideGlobalTooltip();
      });

      marker.on("click", function (e) {
        L.DomEvent.stopPropagation(e);
        if (isMeasuring) {
          hideGlobalTooltip();
          handleAddRoutePoint(marker.getLatLng(), m.name);
          return;
        }
        toggleMarkerTracked(m.id);
        updateGlobalTooltipIfActive(m.id);
      });

      markersCache.set(String(m.id), { data: m, marker: marker });

      if (shouldShowMarker(m)) {
        markersLayerGroup.addLayer(marker);
      }
    });

    renderCustomPins();
  }

  // Check if marker should be visible
  function shouldShowMarker(m) {
    const isCompleted = isMarkerTracked(m.id);

    // Region isolation filter (active when user clicks "Isolate")
    if (isolatedRegion && m.zone !== isolatedRegion) {
      return false;
    }

    // Hide completed filter
    if (hideCompleted && isCompleted) return false;

    // Category filter
    if (!activeFilters[m.type]) return false;

    // Class filter (only applies to dungeons with aspect)
    if (activeClass && m.type === "Dungeon") {
      const aspectClass = (m.aspect && m.aspect.class) || m.class || "All";
      if (aspectClass !== "All" && aspectClass !== activeClass) {
        return false;
      }
    }

    // Search filter
    if (searchTerm.trim() !== "") {
      const term = searchTerm.toLowerCase();
      const matchName = m.name.toLowerCase().includes(term);
      const matchZone = m.zone.toLowerCase().includes(term);
      const matchType = m.type.toLowerCase().includes(term);
      const matchAspect =
        m.aspect &&
        (m.aspect.name.toLowerCase().includes(term) ||
          m.aspect.description.toLowerCase().includes(term) ||
          (m.aspect.class && m.aspect.class.toLowerCase().includes(term)));
      if (!matchName && !matchZone && !matchType && !matchAspect) {
        return false;
      }
    }

    return true;
  }

  // Filter markers visibility without re-instantiating Leaflet objects
  function applyVisibilityFilters() {
    markersCache.forEach(({ data, marker }) => {
      const visible = shouldShowMarker(data);
      if (visible) {
        if (!markersLayerGroup.hasLayer(marker)) {
          markersLayerGroup.addLayer(marker);
        }
      } else {
        if (markersLayerGroup.hasLayer(marker)) {
          markersLayerGroup.removeLayer(marker);
        }
      }
    });
  }

  // Toggle marker tracked state
  function toggleMarkerTracked(id) {
    const current = isMarkerTracked(id);
    const newState = !current;
    setMarkerTracked(id, newState);

    if (newState) {
      playCollectSound();
    }

    saveTrackedState();

    // Update marker visual icon & tooltip
    const entry = markersCache.get(String(id));
    if (entry) {
      entry.marker.setIcon(createMarkerIcon(entry.data.type, newState));
      updateGlobalTooltipIfActive(id);

      if (hideCompleted && newState) {
        markersLayerGroup.removeLayer(entry.marker);
        hideGlobalTooltip();
      }
    }

    // Update global and region counters
    updateProgressCounters();

    // Sync any open checklist drawer
    updateAllOpenDrawers();
  }

  // CRITICAL ANTI-BUG: Update Counters & Progress Bars
  // Computes strictly from the master window.D4_MARKERS list regardless of active filters
  function updateProgressCounters() {
    const data = window.D4_MARKERS || [];

    // Category counts: { type: { found, total } }
    const catCounts = {
      "Altar of Lilith": { found: 0, total: 0 },
      "Tenet of Akarat": { found: 0, total: 0 },
      "Waygate": { found: 0, total: 0 },
      "Dungeon": { found: 0, total: 0 },
      "Stronghold": { found: 0, total: 0 },
      "World Boss": { found: 0, total: 0 },
      "Boss Lair": { found: 0, total: 0 }
    };

    // Region counts: { region: { found, total, altars: [f, t], ... } }
    const regionCounts = {
      "Fractured Peaks": { found: 0, total: 0, altars: [0, 0], strongholds: [0, 0], waypoints: [0, 0], dungeons: [0, 0] },
      "Scosglen": { found: 0, total: 0, altars: [0, 0], strongholds: [0, 0], waypoints: [0, 0], dungeons: [0, 0] },
      "Dry Steppes": { found: 0, total: 0, altars: [0, 0], strongholds: [0, 0], waypoints: [0, 0], dungeons: [0, 0] },
      "Kehjistan": { found: 0, total: 0, altars: [0, 0], strongholds: [0, 0], waypoints: [0, 0], dungeons: [0, 0] },
      "Hawezar": { found: 0, total: 0, altars: [0, 0], strongholds: [0, 0], waypoints: [0, 0], dungeons: [0, 0] },
      "Nahantu": { found: 0, total: 0, altars: [0, 0], strongholds: [0, 0], waypoints: [0, 0], dungeons: [0, 0] }
    };

    // Class aspect counts: { class: { found, total } }
    const classCounts = {
      "Barbarian": { found: 0, total: 0 },
      "Druid": { found: 0, total: 0 },
      "Necromancer": { found: 0, total: 0 },
      "Rogue": { found: 0, total: 0 },
      "Sorcerer": { found: 0, total: 0 },
      "Spiritborn": { found: 0, total: 0 }
    };

    let grandTotal = 0;
    let grandFound = 0;

    data.forEach((m) => {
      if (m.type === "ZoneName") return;

      const isFound = isMarkerTracked(m.id);
      grandTotal++;
      if (isFound) grandFound++;

      if (catCounts[m.type]) {
        catCounts[m.type].total++;
        if (isFound) catCounts[m.type].found++;
      }

      if (regionCounts[m.zone]) {
        const r = regionCounts[m.zone];
        r.total++;
        if (isFound) r.found++;

        if (m.type === "Altar of Lilith" || m.type === "Tenet of Akarat") {
          r.altars[1]++;
          if (isFound) r.altars[0]++;
        } else if (m.type === "Stronghold") {
          r.strongholds[1]++;
          if (isFound) r.strongholds[0]++;
        } else if (m.type === "Waygate") {
          r.waypoints[1]++;
          if (isFound) r.waypoints[0]++;
        } else if (m.type === "Dungeon") {
          r.dungeons[1]++;
          if (isFound) r.dungeons[0]++;
        }
      }

      // Class aspects count (only dungeons granting class codex)
      if (m.type === "Dungeon" && m.aspect) {
        const cls = m.aspect.class || m.class;
        if (cls === "All") {
          for (const cName of Object.keys(classCounts)) {
            classCounts[cName].total++;
            if (isFound) classCounts[cName].found++;
          }
        } else if (cls && classCounts[cls]) {
          classCounts[cls].total++;
          if (isFound) classCounts[cls].found++;
        }
      }
    });

    // Update Category Filter Buttons
    for (const [type, c] of Object.entries(catCounts)) {
      const badge = document.querySelector(`[data-cat-count="${type}"]`);
      if (badge) {
        badge.textContent = `${c.found}/${c.total}`;
        if (c.found === c.total && c.total > 0) {
          badge.classList.add("complete");
        } else {
          badge.classList.remove("complete");
        }
      }
    }

    // Update Region Progress in Sidebar
    for (const [region, r] of Object.entries(regionCounts)) {
      const regBadge = document.querySelector(`[data-region-count="${region}"]`);
      if (regBadge) {
        regBadge.textContent = `${r.found}/${r.total}`;
        if (r.found === r.total && r.total > 0) {
          regBadge.classList.add("complete");
        } else {
          regBadge.classList.remove("complete");
        }
      }

      const regBar = document.querySelector(`[data-region-bar="${region}"]`);
      if (regBar) {
        const pct = r.total > 0 ? (r.found / r.total) * 100 : 0;
        regBar.style.width = `${pct}%`;
      }

      const altarsBadge = document.querySelector(`[data-sub-altar="${region}"]`);
      if (altarsBadge) altarsBadge.textContent = `${r.altars[0]}/${r.altars[1]}`;

      const strongholdsBadge = document.querySelector(`[data-sub-stronghold="${region}"]`);
      if (strongholdsBadge) strongholdsBadge.textContent = `${r.strongholds[0]}/${r.strongholds[1]}`;

      const waypointsBadge = document.querySelector(`[data-sub-waypoint="${region}"]`);
      if (waypointsBadge) waypointsBadge.textContent = `${r.waypoints[0]}/${r.waypoints[1]}`;

      const dungeonsBadge = document.querySelector(`[data-sub-dungeon="${region}"]`);
      if (dungeonsBadge) dungeonsBadge.textContent = `${r.dungeons[0]}/${r.dungeons[1]}`;
    }

    // Update Class Badges
    for (const [cls, c] of Object.entries(classCounts)) {
      const badge = document.querySelector(`[data-class-count="${cls}"]`);
      if (badge) badge.textContent = `${c.found}/${c.total}`;
    }

    // Update Global Progress Bar
    const globalPct = grandTotal > 0 ? Math.round((grandFound / grandTotal) * 100) : 0;
    const globalBar = document.getElementById("globalProgressBar");
    const globalText = document.getElementById("globalProgressText");
    if (globalBar) globalBar.style.width = `${globalPct}%`;
    if (globalText) globalText.textContent = `Explored: ${globalPct}% (${grandFound}/${grandTotal})`;
  }

  function updateSubregionsIsolation() {
    if (!subregionsEnabled) return;

    if (subregionsLayerGroup) {
      subregionsLayerGroup.eachLayer((layer) => {
        restoreSubregionStyle(layer);
      });
    }

    if (mainRegionsLayerGroup) {
      mainRegionsLayerGroup.eachLayer((geoLayer) => {
        if (geoLayer.eachLayer) {
          geoLayer.eachLayer((l) => {
            const title = l.feature && l.feature.properties ? l.feature.properties.title : null;
            if (isolatedRegion) {
              if (title === isolatedRegion) {
                l.setStyle({ color: "#ffd299", weight: 2.8, opacity: 0.95, dashArray: "" });
              } else {
                l.setStyle({ color: "#2d271e", weight: 1.0, opacity: 0.15, dashArray: "4, 6" });
              }
            } else {
              l.setStyle({ color: "#4e4537", weight: 2.0, opacity: 0.6, dashArray: "4, 6" });
            }
          });
        }
      });
    }
  }

  // Region Isolation (Focus Mode)
  function isolateRegion(regionName) {
    if (isolatedRegion === regionName) {
      resetRegionIsolation();
      return;
    }

    isolatedRegion = regionName;

    // Update Sidebar Item Highlight
    document.querySelectorAll(".region-item").forEach((item) => {
      const r = item.getAttribute("data-region");
      item.classList.toggle("region-filtered", r === regionName);
    });

    // Update Isolate Buttons state and text
    document.querySelectorAll(".btn-isolate-region").forEach((btn) => {
      const r = btn.getAttribute("data-isolate-region");
      const isTarget = (r === regionName);
      btn.classList.toggle("active", isTarget);
      btn.textContent = isTarget ? "Isolated ✓" : "Isolate";
    });

    // Update Map Banner
    const banner = document.getElementById("regionIsolateBanner");
    const bannerName = document.getElementById("isolateRegionName");
    if (banner && bannerName) {
      bannerName.textContent = regionName;
      banner.classList.add("active");
    }

    applyVisibilityFilters();
    updateSubregionsIsolation();
    flyToRegion(regionName);
    updateRouteUI();
    showToast(`Focus Mode: Showing only ${regionName}`);
  }

  function resetRegionIsolation(silent = false) {
    isolatedRegion = null;
    document.querySelectorAll(".region-item").forEach((item) => item.classList.remove("region-filtered"));

    document.querySelectorAll(".btn-isolate-region").forEach((btn) => {
      btn.classList.remove("active");
      btn.textContent = "Isolate";
    });

    const banner = document.getElementById("regionIsolateBanner");
    if (banner) banner.classList.remove("active");

    applyVisibilityFilters();
    updateSubregionsIsolation();
    updateRouteUI();
    if (!silent) {
      showToast("Showing all Sanctuary");
      if (map) {
        map.flyTo([0.68, -0.72], 11, { duration: 1.0 });
      }
    }
  }

  // Region Mass Actions
  function markRegionAll(regionName) {
    const data = window.D4_MARKERS || [];
    let count = 0;
    data.forEach((m) => {
      if (m.zone === regionName && m.type !== "ZoneName") {
        setMarkerTracked(m.id, true);
        const entry = markersCache.get(String(m.id));
        if (entry) {
          entry.marker.setIcon(createMarkerIcon(m.type, true));
        }
        count++;
      }
    });

    hideGlobalTooltip();
    saveTrackedState();
    updateProgressCounters();
    applyVisibilityFilters();
    updateAllOpenDrawers();
    playCollectSound();
    showToast(`Region ${regionName}: ${count} markers marked as completed!`);
  }

  function unmarkRegionAll(regionName) {
    const data = window.D4_MARKERS || [];
    let count = 0;
    data.forEach((m) => {
      if (m.zone === regionName && m.type !== "ZoneName") {
        setMarkerTracked(m.id, false);
        const entry = markersCache.get(String(m.id));
        if (entry) {
          entry.marker.setIcon(createMarkerIcon(m.type, false));
        }
        count++;
      }
    });

    hideGlobalTooltip();

    saveTrackedState();
    updateProgressCounters();
    applyVisibilityFilters();
    updateAllOpenDrawers();
    showToast(`Region ${regionName}: all markers unmarked.`);
  }

  // Checklist Drawer per Region
  function toggleChecklistDrawer(region, type) {
    const drawer = document.querySelector(`.region-checklist-drawer[data-drawer-region="${region}"]`);
    if (!drawer) return;

    // If already open with same type, close it
    if (drawer.classList.contains("open") && drawer.getAttribute("data-active-type") === type) {
      drawer.classList.remove("open");
      drawer.innerHTML = "";
      return;
    }

    drawer.setAttribute("data-active-type", type);
    drawer.classList.add("open");
    renderChecklistDrawer(drawer, region, type);
  }

  function renderChecklistDrawer(drawer, region, type) {
    const prevScroll = drawer.scrollTop;
    const data = window.D4_MARKERS || [];
    const items = data.filter((m) => {
      if (m.zone !== region) return false;
      if (type === "Altar of Lilith") {
        return m.type === "Altar of Lilith" || m.type === "Tenet of Akarat";
      }
      return m.type === type;
    });

    if (items.length === 0) {
      drawer.innerHTML = `<div style="padding:8px; font-size:11px; color:#888;">No items found.</div>`;
      return;
    }

    let html = `<div class="checklist-header">
      <span><b>${escapeHTML(type)}</b> in ${escapeHTML(region)} (${items.length})</span>
      <button class="btn-close-drawer" onclick="window.d4App.closeDrawer('${escapeHTML(region)}')">✕</button>
    </div>`;

    items.forEach((m) => {
      const isDone = isMarkerTracked(m.id);
      const aspectInfo = m.aspect ? `<div class="checklist-aspect">${escapeHTML(m.aspect.name)} (${escapeHTML(m.aspect.class || "All")})</div>` : "";
      html += `
        <div class="checklist-entry ${isDone ? "done" : ""}" data-entry-id="${m.id}">
          <label class="checklist-label">
            <input type="checkbox" class="checklist-checkbox" ${isDone ? "checked" : ""} data-check-id="${m.id}" />
            <span class="checklist-name">${escapeHTML(m.name)}</span>
          </label>
          ${aspectInfo}
          <button class="checklist-locate-btn" title="Locate on map" data-locate-id="${m.id}">📍</button>
        </div>
      `;
    });

    drawer.innerHTML = html;
    if (prevScroll > 0) {
      drawer.scrollTop = prevScroll;
    }

    // Attach checkbox events
    drawer.querySelectorAll(".checklist-checkbox").forEach((cb) => {
      cb.addEventListener("change", (e) => {
        const id = cb.getAttribute("data-check-id");
        toggleMarkerTracked(id);
      });
    });

    // Attach locate events
    drawer.querySelectorAll(".checklist-locate-btn").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const id = btn.getAttribute("data-locate-id");
        teleportToMarker(id);
      });
    });
  }

  function updateAllOpenDrawers() {
    document.querySelectorAll(".region-checklist-drawer.open").forEach((drawer) => {
      const region = drawer.getAttribute("data-drawer-region");
      const type = drawer.getAttribute("data-active-type");
      if (region && type) {
        renderChecklistDrawer(drawer, region, type);
      }
    });
  }

  function closeDrawer(region) {
    const drawer = document.querySelector(`.region-checklist-drawer[data-drawer-region="${region}"]`);
    if (drawer) {
      drawer.classList.remove("open");
      drawer.innerHTML = "";
    }
  }

  // Teleport / Focus to specific marker
  function teleportToMarker(id) {
    const entry = markersCache.get(String(id));
    if (!entry) return;

    map.flyTo(entry.data.coords, 14, { duration: 0.8 });

    setTimeout(() => {
      showGlobalTooltipForMarker(id, 3500);
      const el = entry.marker.getElement();
      if (el) {
        el.querySelector(".d4-marker")?.classList.add("pulsing");
        setTimeout(() => {
          el.querySelector(".d4-marker")?.classList.remove("pulsing");
        }, 2200);
      }
    }, 850);
  }

  // Aspect Search Card handler
  function checkAspectSearch(term) {
    const card = document.getElementById("aspectSearchCard");
    if (!card) return;

    if (!term || term.trim().length < 2) {
      card.classList.remove("visible");
      return;
    }

    const t = term.trim().toLowerCase();
    const data = window.D4_MARKERS || [];
    const match = data.find((m) => {
      return (
        m.type === "Dungeon" &&
        m.aspect &&
        (m.aspect.name.toLowerCase().includes(t) ||
          m.aspect.description.toLowerCase().includes(t) ||
          (m.aspect.class && m.aspect.class.toLowerCase().includes(t)))
      );
    });

    if (match && match.aspect) {
      document.getElementById("aspectSearchName").textContent = match.aspect.name;
      document.getElementById("aspectSearchClass").textContent = `Codex of Power • ${match.aspect.class || "All Classes"} (${match.aspect.type || "Aspect"})`;
      document.getElementById("aspectSearchDungeon").innerHTML = `Dungeon: <b>${escapeHTML(match.name)}</b> (${escapeHTML(match.zone)})`;
      document.getElementById("aspectSearchDesc").innerHTML = formatAspectDescription(match.aspect.description);

      const iconElem = document.getElementById("aspectSearchIcon");
      if (iconElem && match.aspect.icon) iconElem.src = match.aspect.icon;

      const locateBtn = document.getElementById("aspectSearchBtn");
      if (locateBtn) {
        locateBtn.onclick = () => teleportToMarker(match.id);
      }

      card.classList.add("visible");
    } else {
      card.classList.remove("visible");
    }
  }

  // Custom Pins
  function renderCustomPins() {
    customPinsGroup.clearLayers();
    customPins.forEach((pin) => {
      const safeTitle = escapeHTML(pin.title || "Custom Pin");
      const safeNotes = pin.notes ? escapeHTML(pin.notes.trim()) : "";
      const pinIcon = L.divIcon({
        className: "custom-pin-wrapper",
        html: `<div class="custom-pin-marker" title="${safeTitle}">📍</div>`,
        iconSize: [24, 24],
        iconAnchor: [12, 12]
      });
      const marker = L.marker([pin.lat, pin.lng], { icon: pinIcon, keyboard: false });
      const notesHTML = safeNotes ? `<div class="map-tooltip-notes">${safeNotes}</div>` : "";
      marker.bindPopup(`
        <div class="map-tooltip">
          <div class="map-tooltip-title">${safeTitle}</div>
          <div class="map-tooltip-subtitle">Custom Marker</div>
          ${notesHTML}
          <div class="map-tooltip-footer">
            <button class="btn btn-sm btn-primary" onclick="window.d4App.deletePin(${pin.id})">Delete Pin</button>
          </div>
        </div>
      `, { autoPan: false, className: "d4-popup" });
      marker.on("click", function (e) {
        if (isMeasuring) {
          L.DomEvent.stopPropagation(e);
          marker.closePopup();
          handleAddRoutePoint(marker.getLatLng(), safeTitle);
        }
      });
      customPinsGroup.addLayer(marker);
    });
  }

  function handleCreatePin(latlng) {
    const rawTitle = prompt("Enter Pin Name:", "Custom Landmark");
    if (!rawTitle) return;
    const title = rawTitle.trim();
    if (!title) return;
    const notes = (prompt("Enter Note/Details (optional):", "") || "").trim();

    const newPin = {
      id: Date.now(),
      lat: latlng.lat,
      lng: latlng.lng,
      title: title,
      notes: notes
    };

    customPins.push(newPin);
    saveCustomPins();
    renderCustomPins();
    showToast(`Pin added: ${title}`);
    togglePinMode(false);
  }

  function deletePin(pinId) {
    customPins = customPins.filter((p) => p.id !== pinId);
    saveCustomPins();
    renderCustomPins();
    showToast("Pin deleted.");
  }

  // Route Tool
  function handleAddRoutePoint(rawLatLng, label = null) {
    const pt = L.latLng(rawLatLng);
    routePoints.push(pt);

    const ptMarker = L.circleMarker(pt, {
      radius: 6,
      color: "#ffd299",
      weight: 2,
      fillColor: "#e74c3c",
      fillOpacity: 0.95,
      interactive: false,
      pane: "markerPane"
    }).addTo(map);
    routeMarkers.push(ptMarker);

    if (routePolyline) {
      routePolyline.setLatLngs(routePoints);
    } else {
      routePolyline = L.polyline(routePoints, {
        color: "#ff3333",
        weight: 4,
        dashArray: "8, 6",
        opacity: 0.95,
        lineCap: "round",
        lineJoin: "round",
        interactive: false
      }).addTo(map);
    }

    updateRouteUI(label);
  }

  function undoLastRoutePoint() {
    if (routePoints.length === 0) return;
    routePoints.pop();
    const lastMarker = routeMarkers.pop();
    if (lastMarker) map.removeLayer(lastMarker);

    if (routePoints.length > 0) {
      if (routePolyline) routePolyline.setLatLngs(routePoints);
    } else {
      if (routePolyline) {
        map.removeLayer(routePolyline);
        routePolyline = null;
      }
    }
    updateRouteUI();
    showToast(`Waypoint removed (${routePoints.length} remaining).`);
  }

  function clearRoute() {
    routePoints = [];
    if (routePolyline) {
      map.removeLayer(routePolyline);
      routePolyline = null;
    }
    routeMarkers.forEach((m) => map.removeLayer(m));
    routeMarkers = [];
    updateRouteUI();
    showToast("Route cleared.");
  }

  function updateRouteUI(lastLabel = null) {
    const routeClearBtn = document.getElementById("btnClearRoute");
    if (routeClearBtn) {
      routeClearBtn.style.display = routePoints.length > 0 ? "inline-flex" : "none";
    }

    const banner = document.getElementById("routeBanner");
    const bannerText = document.getElementById("routeBannerText");
    const isIso = Boolean(isolatedRegion);

    if (banner) {
      banner.classList.toggle("shifted-down", isIso);
      banner.style.display = isMeasuring ? "flex" : "none";
    }

    if (bannerText && isMeasuring) {
      if (routePoints.length === 0) {
        bannerText.textContent = "Route Mode Active: Click map or markers to draw waypoints";
      } else {
        let totalDist = 0;
        for (let i = 1; i < routePoints.length; i++) {
          totalDist += routePoints[i - 1].distanceTo(routePoints[i]);
        }
        const distStr = totalDist >= 1000
          ? `${(totalDist / 1000).toFixed(2)} km`
          : `${Math.round(totalDist)} m`;

        if (routePoints.length === 1) {
          bannerText.innerHTML = `Point 1 placed${lastLabel ? ` (<b>${escapeHTML(lastLabel)}</b>)` : ""} • Click next location to trace route`;
        } else {
          bannerText.innerHTML = `Route: <b>${routePoints.length} points</b> (${distStr})${lastLabel ? ` • Last: <b>${escapeHTML(lastLabel)}</b>` : ""}`;
        }
      }
    }
  }

  function toggleRouteMode(active) {
    isMeasuring = Boolean(active);
    if (isMeasuring && isPinMode) {
      togglePinMode(false);
    }
    const routeBtn = document.getElementById("btnRouteMode");
    if (routeBtn) {
      routeBtn.classList.toggle("active", isMeasuring);
    }
    updateMapCursor();
    updateRouteUI();
    if (isMeasuring) {
      showToast("Route Tool: Click anywhere or on markers to draw waypoints.");
    }
  }

  // UI Setup & Bindings
  function setupUI() {
    // Audio Toggle
    const soundBtn = document.getElementById("btnToggleSound");
    if (soundBtn) {
      soundBtn.innerHTML = soundEnabled ? "🔊 Sound: On" : "🔈 Sound: Off";
      soundBtn.addEventListener("click", () => {
        soundEnabled = !soundEnabled;
        safeStorageSet("d4_sound_enabled", soundEnabled);
        soundBtn.innerHTML = soundEnabled ? "🔊 Sound: On" : "🔈 Sound: Off";
        showToast(soundEnabled ? "Sound effects enabled." : "Sound effects disabled.");
      });
    }

    // Sidebar toggle
    const toggleBtn = document.getElementById("sidebarToggleBtn");
    const sidebar = document.getElementById("sidebar");
    if (toggleBtn && sidebar) {
      toggleBtn.addEventListener("click", () => {
        sidebar.classList.toggle("collapsed");
        const isCollapsed = sidebar.classList.contains("collapsed");
        toggleBtn.innerHTML = isCollapsed ? "☰ Show Filters" : "✕ Hide Filters";
        setTimeout(() => map.invalidateSize(), 300);
      });
    }

    // Search Input with Debounced Filtering (120ms)
    const searchInput = document.getElementById("searchInput");
    const searchClear = document.getElementById("searchClear");
    let searchDebounceTimer = null;

    if (searchInput) {
      searchInput.addEventListener("input", (e) => {
        searchTerm = e.target.value;
        if (searchClear) {
          searchClear.style.display = searchTerm ? "block" : "none";
        }
        if (searchDebounceTimer) clearTimeout(searchDebounceTimer);
        searchDebounceTimer = setTimeout(() => {
          checkAspectSearch(searchTerm);
          applyVisibilityFilters();
        }, 120);
      });
    }

    if (searchClear && searchInput) {
      searchClear.addEventListener("click", () => {
        if (searchDebounceTimer) clearTimeout(searchDebounceTimer);
        searchInput.value = "";
        searchTerm = "";
        searchClear.style.display = "none";
        checkAspectSearch("");
        applyVisibilityFilters();
      });
    }


    // Category Filter Buttons
    document.querySelectorAll(".filter-btn[data-category]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const cat = btn.getAttribute("data-category");
        activeFilters[cat] = !activeFilters[cat];
        btn.classList.toggle("active", activeFilters[cat]);
        btn.classList.toggle("inactive", !activeFilters[cat]);
        applyVisibilityFilters();
      });
    });

    // Select All / Deselect All
    const selectAllBtn = document.getElementById("btnSelectAll");
    const deselectAllBtn = document.getElementById("btnDeselectAll");
    if (selectAllBtn) {
      selectAllBtn.addEventListener("click", (e) => {
        e.preventDefault();
        Object.keys(activeFilters).forEach((k) => (activeFilters[k] = true));
        document.querySelectorAll(".filter-btn[data-category]").forEach((btn) => {
          btn.classList.add("active");
          btn.classList.remove("inactive");
        });
        applyVisibilityFilters();
      });
    }
    if (deselectAllBtn) {
      deselectAllBtn.addEventListener("click", (e) => {
        e.preventDefault();
        Object.keys(activeFilters).forEach((k) => (activeFilters[k] = false));
        document.querySelectorAll(".filter-btn[data-category]").forEach((btn) => {
          btn.classList.remove("active");
          btn.classList.add("inactive");
        });
        applyVisibilityFilters();
      });
    }

    // Subregions Toggle
    const toggleSubregionsBtn = document.getElementById("btnToggleSubregions");
    if (toggleSubregionsBtn) {
      toggleSubregionsBtn.innerHTML = subregionsEnabled ? "🗺 Subregions: On" : "🗺 Subregions: Off";
      toggleSubregionsBtn.classList.toggle("active", subregionsEnabled);
      toggleSubregionsBtn.addEventListener("click", () => {
        subregionsEnabled = !subregionsEnabled;
        safeStorageSet("d4_subregions_enabled", subregionsEnabled);
        toggleSubregionsBtn.innerHTML = subregionsEnabled ? "🗺 Subregions: On" : "🗺 Subregions: Off";
        toggleSubregionsBtn.classList.toggle("active", subregionsEnabled);
        if (subregionsEnabled) {
          if (!map.hasLayer(mainRegionsLayerGroup)) map.addLayer(mainRegionsLayerGroup);
          if (!map.hasLayer(subregionsLayerGroup)) map.addLayer(subregionsLayerGroup);
          showToast("Subregions & boundaries enabled.");
        } else {
          if (map.hasLayer(mainRegionsLayerGroup)) map.removeLayer(mainRegionsLayerGroup);
          if (map.hasLayer(subregionsLayerGroup)) map.removeLayer(subregionsLayerGroup);
          hideSubregionHover();
          showToast("Subregions & boundaries disabled.");
        }
      });
    }

    // Hide Completed Toggle
    const hideCompletedBtn = document.getElementById("btnToggleCompleted");
    if (hideCompletedBtn) {
      hideCompletedBtn.addEventListener("click", () => {
        hideCompleted = !hideCompleted;
        hideCompletedBtn.classList.toggle("active", hideCompleted);
        hideCompletedBtn.textContent = hideCompleted ? "👁 Show Completed" : "👁‍🗨 Hide Completed";
        applyVisibilityFilters();
      });
    }

    // Class Filters
    document.querySelectorAll(".class-btn[data-class]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const cls = btn.getAttribute("data-class");
        if (activeClass === cls) {
          activeClass = null;
          btn.classList.remove("active");
        } else {
          document.querySelectorAll(".class-btn").forEach((b) => b.classList.remove("active"));
          activeClass = cls;
          btn.classList.add("active");
        }
        applyVisibilityFilters();
      });
    });

    // Region Accordions & Fly-to
    document.querySelectorAll(".region-header").forEach((header) => {
      header.addEventListener("click", (e) => {
        if (e.target.closest(".region-btn-tool")) return;
        const item = header.closest(".region-item");
        item.classList.toggle("expanded");
      });
    });

    // Region Fly Buttons
    document.querySelectorAll(".region-fly-btn").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const region = btn.getAttribute("data-fly-region");
        flyToRegion(region);
      });
    });

    // Region Isolate Buttons
    document.querySelectorAll(".btn-isolate-region").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const region = btn.getAttribute("data-isolate-region");
        isolateRegion(region);
      });
    });

    // Exit Region Isolation
    const btnExitIsolate = document.getElementById("btnExitRegionIsolate");
    const btnResetRegionFilter = document.getElementById("btnResetRegionFilter");
    if (btnExitIsolate) btnExitIsolate.addEventListener("click", resetRegionIsolation);
    if (btnResetRegionFilter) btnResetRegionFilter.addEventListener("click", resetRegionIsolation);

    // Region Mass Actions (Mark All / Unmark All)
    document.querySelectorAll(".btn-mark-region-all").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const r = btn.getAttribute("data-target-region");
        markRegionAll(r);
      });
    });

    document.querySelectorAll(".btn-unmark-region-all").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const r = btn.getAttribute("data-target-region");
        unmarkRegionAll(r);
      });
    });

    // Region Sub-progress Checklist Drawer Toggles
    document.querySelectorAll("[data-toggle-checklist]").forEach((el) => {
      el.addEventListener("click", (e) => {
        e.stopPropagation();
        const region = el.getAttribute("data-toggle-checklist");
        const type = el.getAttribute("data-check-type");
        toggleChecklistDrawer(region, type);
      });
    });

    // Global Keyboard Handler: Block Tab recenter and handle Escape
    document.addEventListener("keydown", (e) => {
      // Prevent Tab key from cycling focus, jumping Leaflet panes, or triggering recenter
      if (e.key === "Tab") {
        e.preventDefault();
        return;
      }
      if (e.key === "Escape") {
        const modal = document.getElementById("clearModal");
        if (modal) modal.classList.remove("active");
        if (isPinMode) togglePinMode(false);
        if (isMeasuring) toggleRouteMode(false);
      }
    });

    // Clear Progress Modal
    const clearBtn = document.getElementById("btnClearProgress");
    const modal = document.getElementById("clearModal");
    const confirmClear = document.getElementById("btnConfirmClear");
    const cancelClear = document.getElementById("btnCancelClear");

    if (clearBtn && modal) {
      clearBtn.addEventListener("click", () => {
        modal.classList.add("active");
      });
    }
    if (cancelClear && modal) {
      cancelClear.addEventListener("click", () => modal.classList.remove("active"));
    }
    if (modal) {
      modal.addEventListener("click", (e) => {
        if (e.target === modal) modal.classList.remove("active");
      });
    }
    if (confirmClear && modal) {
      confirmClear.addEventListener("click", () => {
        trackedMarkers = {};
        saveTrackedState();
        renderMarkers();
        updateProgressCounters();
        updateAllOpenDrawers();
        modal.classList.remove("active");
        showToast("Cleared all tracked markers");
      });
    }

    // Export Progress
    const exportBtn = document.getElementById("btnExport");
    if (exportBtn) {
      exportBtn.addEventListener("click", exportProgressData);
    }

    // Import Progress
    const importBtn = document.getElementById("btnImport");
    const importInput = document.getElementById("importFileInput");
    if (importBtn && importInput) {
      importBtn.addEventListener("click", () => importInput.click());
      importInput.addEventListener("change", importProgressData);
    }

    // Custom Pin Mode Toggle
    const pinModeBtn = document.getElementById("btnPinMode");
    if (pinModeBtn) {
      pinModeBtn.addEventListener("click", () => {
        togglePinMode(!isPinMode);
      });
    }

    // Route Tool Toggle & Clear
    const routeBtn = document.getElementById("btnRouteMode");
    const routeClearBtn = document.getElementById("btnClearRoute");
    if (routeBtn) {
      routeBtn.addEventListener("click", () => {
        toggleRouteMode(!isMeasuring);
      });
    }
    if (routeClearBtn) {
      routeClearBtn.addEventListener("click", clearRoute);
    }

    // Route Banner Actions
    const btnUndoRoute = document.getElementById("btnUndoRoutePoint");
    if (btnUndoRoute) {
      btnUndoRoute.addEventListener("click", undoLastRoutePoint);
    }
    const btnClearRouteBanner = document.getElementById("btnClearRouteBanner");
    if (btnClearRouteBanner) {
      btnClearRouteBanner.addEventListener("click", clearRoute);
    }
    const btnDoneRoute = document.getElementById("btnDoneRoute");
    if (btnDoneRoute) {
      btnDoneRoute.addEventListener("click", () => {
        toggleRouteMode(false);
        showToast(`Route finished: ${routePoints.length} waypoints on map.`);
      });
    }
  }

  function updateMapCursor() {
    const mapEl = document.getElementById("map");
    if (mapEl) {
      mapEl.classList.toggle("cursor-crosshair", Boolean(isPinMode || isMeasuring));
    }
  }

  function togglePinMode(active) {
    isPinMode = Boolean(active);
    if (isPinMode && isMeasuring) {
      toggleRouteMode(false);
    }
    const btn = document.getElementById("btnPinMode");
    if (btn) btn.classList.toggle("active", isPinMode);
    updateMapCursor();
    if (isPinMode) {
      showToast("Pin Mode: Click anywhere on map to add custom pin.");
    }
  }

  function getRegionBounds(region) {
    const latLngs = [];
    // 1. Include region polygon from GeoJSON if available
    if (window.D4_REGIONS_GEOJSON && Array.isArray(window.D4_REGIONS_GEOJSON.features)) {
      const feat = window.D4_REGIONS_GEOJSON.features.find((f) => f.properties && f.properties.title === region);
      if (feat && feat.geometry && feat.geometry.coordinates) {
        const extractCoords = (coords) => {
          if (typeof coords[0] === "number") {
            // GeoJSON is [lng, lat] -> Leaflet is [lat, lng]
            latLngs.push(L.latLng(coords[1], coords[0]));
          } else {
            coords.forEach(extractCoords);
          }
        };
        extractCoords(feat.geometry.coordinates);
      }
    }
    // 2. Include all markers in the region
    markersCache.forEach(({ data, marker }) => {
      if (data.zone === region && data.type !== "ZoneName") {
        latLngs.push(marker.getLatLng());
      }
    });
    if (latLngs.length > 0) {
      return L.latLngBounds(latLngs);
    }
    const meta = REGION_BOUNDS[region];
    return meta ? L.latLngBounds(meta.bounds) : null;
  }

  function flyToRegion(region) {
    if (!map) return;
    const bounds = getRegionBounds(region);
    if (bounds && bounds.isValid()) {
      map.flyToBounds(bounds, {
        padding: [45, 45],
        maxZoom: 13,
        duration: 0.9
      });
      showToast(`Centered on: ${region}`);
    }
  }

  // Export Data JSON
  function exportProgressData() {
    const payload = {
      version: "2.5",
      exportDate: new Date().toISOString(),
      realm: currentRealm,
      totalMarked: Object.keys(trackedMarkers).length,
      trackedMarkers: trackedMarkers,
      customPins: customPins
    };
    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = "d4_map_backup_eternal.json";
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
    showToast("Backup exported successfully!");
  }

  // Import Data JSON
  function importProgressData(e) {
    const file = e.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = function (evt) {
      try {
        const data = JSON.parse(evt.target.result);
        if (data.trackedMarkers && typeof data.trackedMarkers === "object") {
          // Normalize imported keys
          const norm = {};
          for (const [k, v] of Object.entries(data.trackedMarkers)) {
            if (v) norm[String(k)] = true;
          }
          trackedMarkers = norm;
          saveTrackedState();

          if (Array.isArray(data.customPins)) {
            customPins = data.customPins;
            saveCustomPins();
            renderCustomPins();
          }

          renderMarkers();
          updateProgressCounters();
          updateAllOpenDrawers();
          showToast(`Import completed: ${Object.keys(norm).length} markers loaded!`);
        } else {
          showToast("Invalid backup file format.");
        }
      } catch (err) {
        showToast("Error parsing JSON file: " + err.message);
      }
    };
    reader.readAsText(file);
    e.target.value = "";
  }

  // Toast notifications
  function showToast(msg) {
    const container = document.getElementById("toastContainer");
    if (!container) return;
    const t = document.createElement("div");
    t.className = "toast";
    t.textContent = msg;
    container.appendChild(t);
    setTimeout(() => {
      t.style.opacity = "0";
      t.style.transition = "opacity 0.3s";
      setTimeout(() => {
        if (container.contains(t)) container.removeChild(t);
      }, 300);
    }, 2500);
  }

  // Expose global methods for inline HTML onclick handlers
  window.d4App = {
    deletePin: deletePin,
    flyToRegion: flyToRegion,
    isolateRegion: isolateRegion,
    markRegionAll: markRegionAll,
    unmarkRegionAll: unmarkRegionAll,
    closeDrawer: closeDrawer,
    teleportToMarker: teleportToMarker,
    toggleRouteMode: toggleRouteMode,
    clearRoute: clearRoute,
    undoLastRoutePoint: undoLastRoutePoint,
    getMap: function () { return map; },
    REGION_BOUNDS: REGION_BOUNDS
  };

  // Start app on DOM ready
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
