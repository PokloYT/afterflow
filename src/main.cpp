#include <Geode/Geode.hpp>
#include <Geode/utils/general.hpp>
#include <Geode/utils/async.hpp>
#include <Geode/utils/VersionInfo.hpp>
#include <Geode/utils/web.hpp>
#include <Geode/loader/SettingV3.hpp>
#include <Geode/utils/Keyboard.hpp>
#include <Geode/ui/GeodeUI.hpp>
#include <Geode/ui/Popup.hpp>
#include <Geode/modify/MenuLayer.hpp>
#include <Geode/modify/EffectGameObject.hpp>
#include <Geode/modify/GJBaseGameLayer.hpp>
#include <Geode/modify/GameObject.hpp>
#include <Geode/modify/HardStreak.hpp>
#include <Geode/modify/LevelEditorLayer.hpp>
#include <Geode/modify/PlayLayer.hpp>
#include <Geode/modify/PlayerObject.hpp>
#include <Geode/modify/RingObject.hpp>
#include <algorithm>
#include <cctype>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cmath>
#include <cwctype>
#include <deque>
#include <filesystem>
#include <fstream>
#include <functional>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#ifdef _WIN32
#include <windows.h>
#include <shellapi.h>
#endif

#ifdef GEODE_IS_MACOS
#include <signal.h>
#include <sys/types.h>
#include <unistd.h>
#endif

using namespace geode::prelude;

namespace {

    constexpr int MOD_HOOK_PRIORITY = -1000000;
    constexpr float TICK_DURATION = 0.25f;
    constexpr char const* KEYBIND_STAGE = "keybind-stage";
    constexpr char const* KEYBIND_TERMINAL = "keybind-terminal";
    constexpr char const* KEYBIND_INTRO_DONE = "keybind-intro-done";

#ifdef _WIN32
    HANDLE g_terminalLogHandle = INVALID_HANDLE_VALUE;
    std::string g_windowsTerminalLogFileName = "afterflow-terminal.log";
#endif

    constexpr uint64_t typeBit(GameObjectType objectType) {
        return 1ull << static_cast<int>(objectType);
    }

    constexpr uint64_t COLLIDING_OBJECT_TYPES = typeBit(GameObjectType::Solid) | typeBit(GameObjectType::Hazard) | typeBit(GameObjectType::Slope) |
                                         typeBit(GameObjectType::CollisionObject) | typeBit(GameObjectType::AnimatedHazard);

    constexpr uint64_t HAZARD_OBJECT_TYPES = typeBit(GameObjectType::Hazard) | typeBit(GameObjectType::AnimatedHazard);

    constexpr uint64_t INTERACTABLE_OBJECT_TYPES =
        typeBit(GameObjectType::YellowJumpPad) | typeBit(GameObjectType::PinkJumpPad) | typeBit(GameObjectType::RedJumpPad) |
        typeBit(GameObjectType::GravityPad) | typeBit(GameObjectType::SpiderPad) | typeBit(GameObjectType::YellowJumpRing) |
        typeBit(GameObjectType::PinkJumpRing) | typeBit(GameObjectType::RedJumpRing) | typeBit(GameObjectType::GravityRing) |
        typeBit(GameObjectType::GreenRing) | typeBit(GameObjectType::DropRing) | typeBit(GameObjectType::CustomRing) |
        typeBit(GameObjectType::DashRing) | typeBit(GameObjectType::GravityDashRing) | typeBit(GameObjectType::SpiderOrb) |
        typeBit(GameObjectType::InverseGravityPortal) | typeBit(GameObjectType::NormalGravityPortal) |
        typeBit(GameObjectType::GravityTogglePortal);

    constexpr uint64_t MODE_PORTAL_OBJECT_TYPES =
        typeBit(GameObjectType::ShipPortal) | typeBit(GameObjectType::CubePortal) | typeBit(GameObjectType::BallPortal) |
        typeBit(GameObjectType::UfoPortal) | typeBit(GameObjectType::WavePortal) | typeBit(GameObjectType::RobotPortal) |
        typeBit(GameObjectType::SpiderPortal) | typeBit(GameObjectType::SwingPortal) | typeBit(GameObjectType::DualPortal) |
        typeBit(GameObjectType::SoloPortal) | typeBit(GameObjectType::TeleportPortal) | typeBit(GameObjectType::TeleportOrb);

    constexpr uint64_t SIZE_PORTAL_OBJECT_TYPES = typeBit(GameObjectType::RegularSizePortal) | typeBit(GameObjectType::MiniSizePortal);

    constexpr int HOLD_SAMPLE_COUNT = 8;
    constexpr int SPIDER_LAND_TICKS = 12;
    constexpr int SPAM_STREAK_COUNT = 3;
    constexpr int WAVE_TURN_MARGIN_TICKS[] = { 4, 8, 12 };
    constexpr int WAVE_MIN_TURN_TICKS = 6;
    constexpr int WAVE_ESCAPE_TICKS = 16;
    constexpr int ROBOT_HOLD_TICKS[] = { 6, 14, 26, 45 };
    constexpr int SPIDER_RETAP_TICKS[] = { 4, 8, 12 };
    constexpr int SPIDER_MIN_RETAP_TICKS = 4;
    constexpr int SAME_CRASH_TRY_COUNT = 4;
    constexpr int SHIP_RECOVERY_TICKS[] = { 8, 16, 24 };
    constexpr int UFO_REFLAP_TICKS[] = { 6, 12, 18 };

    bool hasType(uint64_t typeMask, GameObject* gameObject) {
        auto objectType = static_cast<unsigned>(gameObject->m_objectType);
        return objectType < 64 && ((typeMask >> objectType) & 1);
    }

    float speedPortalValue(int objectId) {
        switch (objectId) {
            case 200: return 0.7f;
            case 201: return 0.9f;
            case 202: return 1.1f;
            case 203: return 1.3f;
            case 1334: return 1.6f;
            default: return 0.f;
        }
    }

    struct Stage {
        bool isEnabled;
        int ticksAllModes;
        int ticksWaveMode;
        bool isCustom;
    };

    constexpr Stage STAGE_TABLE[] = {
        { true, 2, 2, false },
        { true, 4, 4, false },
        { true, 8, 8, false },
        { true, 16, 8, false },
        { true, 24, 12, false },
        { true, 32, 16, false },
        { true, 40, 20, false },
        { false, 0, 0, false },
    };
    constexpr int STAGE_TABLE_SIZE = sizeof(STAGE_TABLE) / sizeof(STAGE_TABLE[0]);

    struct QueuedInput {
        int ticksRemaining;
        bool isDown;
    };

    struct ObjSnapshot {
        GameObject* gameObject;
        bool isObjectActivated;
        EffectGameObject* effectObject;
        bool isActivatedByEffect;
        bool byPlayer1;
        bool byPlayer2;
    };

    struct ProbeOrb {
        RingObject* ringObject = nullptr;
        PlayerObject* playerObject = nullptr;
        float touchDistanceSquared = 0.f;
        float closeDistanceSquared = 0.f;
        int touchSampleTick = -1;
        int closeSampleTick = -1;
    };

    struct HoldStats {
        int holdSamples[HOLD_SAMPLE_COUNT] = {};
        int sampleCount = 0;
        int nextSampleIndex = 0;

        void add(int tickCount) {
            holdSamples[nextSampleIndex] = std::clamp(tickCount, 1, 240);
            nextSampleIndex = (nextSampleIndex + 1) % HOLD_SAMPLE_COUNT;
            sampleCount = std::min(sampleCount + 1, HOLD_SAMPLE_COUNT);
        }

        int pick(int fallbackValue, int percentile) const {
            if (sampleCount == 0) {
                return fallbackValue;
            }
            int scratchSamples[HOLD_SAMPLE_COUNT];
            std::copy(holdSamples, holdSamples + sampleCount, scratchSamples);
            int sampleIndex = std::min(sampleCount - 1, sampleCount * percentile / 100);
            std::nth_element(scratchSamples, scratchSamples + sampleIndex, scratchSamples + sampleCount);
            return scratchSamples[sampleIndex];
        }
    };

    enum class InputKind { Tap, Wave, Robot, Other };

    struct Buffer {

        PlayerObject* ghostPlayer1 = nullptr;
        PlayerObject* ghostPlayer2 = nullptr;
        CCLayer* ghostRenderLayer = nullptr;
        unsigned ghostLayerBaseIndex = 0;
        bool performanceMode = false;
        double userBudgetMilliseconds = 6.0;
        bool automaticBudget = true;
        int keyStates[6] = { 0, 0, 0, 0, 0, 0 };
        std::unordered_set<GameObject*> simulationDisabledObjects;

        bool isSimulating = false;
        bool isInjecting = false;
        bool hasGhostDied = false;
        bool hasGhostHitPortal = false;
        bool hasRealInput = false;
        bool hasAppliedInput = false;
        bool isFirstPlayer = true;

        bool isEnabled = true;
        int stageIndex = 0;
        int ticksAllModes = 2;
        int ticksWaveMode = 2;

        std::deque<QueuedInput> queuedInputs;
        int inputShiftTicks = 0;

        float tickLengthSeconds = TICK_DURATION;
        int ticksSinceInput = 999;
        int rapidInputTicks = 0;

        bool smartEnabled = true;
        bool consoleEnabled = false;
        double budgetMilliseconds = 6.0;
        bool practiceModeOnly = true;
        int groundHorizonTicks = 130;
        int releaseShiftTicks = 0;
        int waveHorizonTicks = 65;
        bool assumeOrbHits = true;
        bool isHeld1 = false, isHeld2 = false;
        bool isAuto1 = false, isAuto2 = false;
        bool orbTimingEnabled = true;
        int orbClickDelayTicks = 0;
        int autoReleaseTick1 = -1, autoReleaseTick2 = -1;
        bool wasOrbTiming = false;
        bool tryBothOrbCandidates = true;
        bool orbClickEnabled = true;
        bool hasTouchedOrb = false;
        bool skipPressHandling = false;
        bool avoidMovingObjects = true;
        bool hasSeenMover = false;
        bool trackMovingObjects = false;
        bool autoReleaseEnabled = false;
        int autoReleaseWindowTicks = 6;
        bool wasAutoReleased = false;
        int spamGapTicks = 16;
        bool waveMarginEnabled = true;
        bool waveVersion46Mode = false;
        bool orbAlignEnabled = true;
        bool orbAlignToGround = false;
        bool ignoreTouchingObjects = true;
        bool hasRealRectangle = false;
        CCRect realRectanglePlayer1, realRectanglePlayer2;
        std::unordered_set<GameObject*> harmlessObjects;
        int baseEscapeTicks = -1;
        int baseCrashTicks = -1;

        bool lowLatencyMode = false;
        bool explainEnabled = false;
        bool deathLogEnabled = false;
        bool captureKillerObject = false;
        bool hasBaseTouchedDown = false;
        bool hasSeenKiller = false;
        int killerCollisionTick = -1;
        int killerObjectId = 0, killerObjectType = -1;
        bool killerWithoutTouch = false, isKillerDisabled = false;
        CCRect killerRectangle, ghostDeathRectangle;
        bool robustSaveMode = true;
        float ghostHorizontalShift = 0.f;
        int lateCrashTicks = 90;
        bool predictMovingObjects = false;
        bool shipBufferEnabled = false;
        int shipSpamGapTicks = 6;
        int shipMaxDelayTicks = 2;

        bool performanceLogEnabled = false;
        int simulationRunCount = 0;
        long simulatedTickCount = 0;
        bool clickBetweenFramesSync = true;
        float firstStepScale = 1.f;
        bool isInRealUpdate = false;
        float tickStartPositionX = 0.f;
        float tickDeltaX = 0.f;
        bool dashAutoReleaseEnabled = false;
        bool autoDashEnabled = false;
        std::unordered_set<GameObject*> usedOrbs;
        bool moreTimeEnabled = true;
        bool ballSmartEnabled = true;
        bool swingSmartEnabled = true;
        bool trainingMode = false;
        bool perLevelStats = true;
        bool heatmapEnabled = true;

        CCLabelBMFont* hintTextLabel = nullptr;
        CCDrawNode* heatmapNode = nullptr;
        bool ufoSmartEnabled = true;
        bool spiderSmartEnabled = true;
        int retapTick = -1;
        bool robotSmartEnabled = true;
        bool robotAutoReleaseEnabled = false;
        bool autoNormalRunsEnabled = false;
        CCLabelBMFont* autoTagLabel = nullptr;
        CCLabelBMFont* watermarkLabel = nullptr;
        bool wasUsedThisAttempt = false;
        bool learningEnabled = true;
        bool fullSimulationState = true;

        int orbWindowTicks = 6;
        int simulationTick = 0;
        int firstOrbTouchTick = -1;
        int orbUseTick = -1;
        RingObject* firstOrbRingObject = nullptr;
        PlayerObject* firstOrbPlayerObject = nullptr;
        int orbCloseSampleTick = -1;
        float orbTouchDistanceSquared = 0.f;
        float orbCloseDistanceSquared = 0.f;
        RingObject* intendedOrbObject = nullptr;
        RingObject* pressOrbRingObject = nullptr;
        int inputTickIndex = 0;
        bool isInputDown = false;
        std::vector<ProbeOrb> probeOrbCandidates;
        bool isProbing = false;
        bool driftCheckEnabled = false;
        std::vector<CCPoint>* recordedPath = nullptr;
        bool showPathEnabled = false;
        CCDrawNode* pathDrawNode = nullptr;
        int pathHoldUntilTick = 0;

        std::unordered_set<GameObject*> simulationUsedObjects;
        std::vector<ObjSnapshot> objectSnapshots;
    } state;

    HoldStats tapHoldHistory, robotHoldHistory;
    int currentTick = 0;
    int lastPressTick = -1;
    InputKind lastPressKind = InputKind::Other;
    std::chrono::steady_clock::time_point clickStartTime;
    int debugBestDelay = 0;
    int debugBestResult = -1;
    int robotUsedHoldTicks = -1;
    bool isQuickScore = false;
    bool isCrashFixed = false;
    bool isMarginUsed = false;

    void cycleStage(int direction);
    void toggleTerminal() {} // Заглушка для Android
    std::string stageText();

    float stepScale() {
        float deltaTime = state.tickLengthSeconds;
        if (!(deltaTime > 0.001f && deltaTime < 2.f)) {
            return 1.f;
        }
        return std::clamp(TICK_DURATION / deltaTime, 0.25f, 8.f);
    }

    int st(int ticksAt240Hz) {
        if (ticksAt240Hz <= 0) {
            return ticksAt240Hz;
        }
        return std::max(1, static_cast<int>(std::lround(ticksAt240Hz * stepScale())));
    }

    // Заглушки для десктопних функцій, щоб вони не викликали помилок компіляції на Android
    bool isTerminalEnabled() {
        return false;
    }

    void writeTerminalFlags() {}
}

// Додаємо базовий клас або ініціалізацію моду через $execute для Android
$execute {
    log::info("Afterflow loaded on Android!");
}
