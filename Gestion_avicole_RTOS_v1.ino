#include <stdio.h>
#include <string.h>
#include <math.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/event_groups.h"
#include "esp_system.h"
#include "esp_log.h"
#include "esp_wifi.h"
#include "esp_now.h"
#include "nvs_flash.h"
#include "driver/gpio.h"
#include "driver/spi_master.h"
#include "driver/i2c.h"
#include "esp_netif.h"

// =============================================================================
// CONFIGURATION DES PINS ET CONSTANTES
// =============================================================================

static const char *TAG = "CENTRALE";

// ----- Module LoRa SX1278 (RA-02, 433 MHz) -----
#define LORA_NSS_PIN    5    // NSS/CS
#define LORA_RST_PIN    14   // Reset
#define LORA_DIO0_PIN   2    // DIO0
#define LORA_SCK_PIN    18   // SPI SCK
#define LORA_MISO_PIN   19   // SPI MISO
#define LORA_MOSI_PIN   23   // SPI MOSI
#define LORA_FREQUENCY  433E6  // 433 MHz

// ----- Relais -----
#define NUM_RELAYS      8
static const int relayPins[NUM_RELAYS] = {13, 12, 14, 27, 26, 25, 33, 32};

// Seuils et délais
#define DATA_TIMEOUT_MS     300000  // 5 minutes sans données
const float GAS_ALARM_THRESHOLD   = 2000.0f;
const float TEMP_ALARM_MARGIN     = 5.0f;
const float HUMIDITY_ALARM_MARGIN = 15.0f;
const uint16_t TVOC_THRESHOLD     = 600;
const uint16_t ECO2_THRESHOLD     = 1000;

// Attribution des relais (indices dans relayPins)
#define VENTILATION_1   0
#define VENTILATION_2   1
#define CHAUFFAGE_1     2
#define CHAUFFAGE_2     3
#define BRUMISATION     4
#define ECLAIRAGE       5
#define POMPE_EAU       6
#define ALARME          7

// ----- WiFi AP pour le HMI -----
#define WIFI_SSID       "ESP32_Relay"
#define WIFI_PASS       "production_password"
#define WIFI_CHANNEL    1
#define MAX_STA_CONN    4

// =============================================================================
// STRUCTURES DE DONNÉES
// =============================================================================

// Paramètres d'élevage
typedef struct {
    uint8_t ageInDays;
    float targetTemp;
    float tempMargin;
    float targetHumidity;
    float humidityMargin;
    uint8_t lightHoursPerDay;
    bool autoMode;
} BreedingParameters;

// Configuration par densité
typedef struct {
    int minPoulets;
    int maxPoulets;
    float targetTemp;
    float targetHumidity;
    uint8_t lightHoursPerDay;
} DensityRange;

static const DensityRange densityConfigs[] = {
    {100, 1000, 33.0, 60.0, 24},
    {1001, 5000, 32.0, 62.0, 23},
    {5001, 10000, 31.0, 64.0, 22}
};

// Données d'un capteur (envoyées via LoRa)
typedef struct {
    uint32_t sensorId;      // Par exemple, 6 derniers caractères de l'adresse MAC
    float temperature;
    float humidity;
    float gasLevel;
    float waterFlow;
    unsigned long timestamp;
    uint16_t tvoc;
    uint16_t eco2;
} SensorData;

// État des relais
typedef struct {
    bool relayStates[NUM_RELAYS];
} RelayStatus;

// Structures de commandes HMI (pour configuration et gestion)
typedef struct {
    int nombrePoulets;
} HMIConfig;

typedef struct {
    uint8_t second;
    uint8_t minute;
    uint8_t hour;
    uint8_t day;
    uint8_t month;
    uint16_t year;
} HMIClockConfig;

typedef struct {
    uint8_t command; // 1 = reset
} HMIResetCommand;

typedef struct {
    char mode[3];    // "CR" ou "SR"
    int securityCode; 
} HMIProductionMode;

typedef struct {
    SensorData sensors;
    RelayStatus relays;
    BreedingParameters params;
    int nombrePoulets;
} CombinedData;

typedef struct {
    uint8_t command; // 1 = ajouter, 0 = retirer
    uint32_t sensorId;
} HMISensorAuthCommand;

// Pour la gestion des capteurs autorisés
#define MAX_SENSORS 50
static uint32_t authorizedSensors[MAX_SENSORS];
static int numAuthorizedSensors = 0;

typedef struct {
    uint32_t id;
    SensorData data;
    unsigned long lastUpdate;
} SensorNode;
static SensorNode sensorNodes[MAX_SENSORS];
static int numSensors = 0;

// =============================================================================
// VARIABLES GLOBALES
// =============================================================================

static SensorData sensorData;       // Données agrégées (moyenne)
static SensorData lastValidSensorData;
static RelayStatus relayData;
static CombinedData combinedData;
static BreedingParameters currentParams;
static int nombrePoulets = 1000;
static char productionMode[3] = "CR";

static unsigned long lastControlUpdate = 0;
static unsigned long lastDataReceived = 0;
static bool dataAlert = false;

// Paramètres par âge
static const BreedingParameters AGE_PARAMETERS[] = {
    {0,  33.0, 0.5, 60.0, 5.0, 24, true},
    {7,  31.0, 0.5, 60.0, 5.0, 23, true},
    {14, 29.0, 1.0, 60.0, 5.0, 22, true},
    {21, 27.0, 1.0, 65.0, 5.0, 21, true},
    {28, 25.0, 1.0, 65.0, 5.0, 20, true},
    {35, 23.0, 1.5, 65.0, 5.0, 18, true},
    {42, 21.0, 1.5, 65.0, 5.0, 17, true}
};

// =============================================================================
// PILOTES DS1302 (RTC)
// =============================================================================
// Le DS1302 utilise une interface 3 fils (RST, DATA, CLK). Ces fonctions stubs
// doivent être adaptées à votre driver.
#define DS1302_RST_PIN   4    
#define DS1302_IO_PIN    16   
#define DS1302_CLK_PIN   17   

typedef struct {
    int second;
    int minute;
    int hour;
    int day;
    int month;
    int year;
} DS1302_Time;

static DS1302_Time rtc_time;

void ds1302_init(void)
{
    gpio_reset_pin(DS1302_RST_PIN);
    gpio_set_direction(DS1302_RST_PIN, GPIO_MODE_OUTPUT);
    gpio_reset_pin(DS1302_CLK_PIN);
    gpio_set_direction(DS1302_CLK_PIN, GPIO_MODE_OUTPUT);
    // DS1302_IO_PIN sera géré en mode bidirectionnel.
    ESP_LOGI(TAG, "DS1302 initialisé");
}

void ds1302_get_time(DS1302_Time *time)
{
    // Implémenter la lecture effective du DS1302.
    // Pour ce stub, on renvoie une heure fixe.
    time->second = 0;
    time->minute = 0;
    time->hour   = 6;
    time->day    = 1;
    time->month  = 1;
    time->year   = 2025;
}

void ds1302_set_time(DS1302_Time *time)
{
    ESP_LOGI(TAG, "DS1302 mis à jour: %04d-%02d-%02d %02d:%02d:%02d",
             time->year, time->month, time->day, time->hour, time->minute, time->second);
}

// =============================================================================
// WIFI EN MODE AP (pour que le HMI se connecte)
// =============================================================================

static void wifi_init_softap(void)
{
    ESP_LOGI(TAG, "Configuration du WiFi en mode AP");
    esp_netif_create_default_wifi_ap();
    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    esp_wifi_init(&cfg);
    
    wifi_config_t wifi_config = { 0 };
    strncpy((char *)wifi_config.ap.ssid, WIFI_SSID, sizeof(wifi_config.ap.ssid));
    wifi_config.ap.ssid_len = strlen(WIFI_SSID);
    strncpy((char *)wifi_config.ap.password, WIFI_PASS, sizeof(wifi_config.ap.password));
    wifi_config.ap.channel = WIFI_CHANNEL;
    wifi_config.ap.max_connection = MAX_STA_CONN;
    wifi_config.ap.authmode = strlen(WIFI_PASS) ? WIFI_AUTH_WPA_WPA2_PSK : WIFI_AUTH_OPEN;
    
    esp_wifi_set_mode(WIFI_MODE_AP);
    esp_wifi_set_config(WIFI_IF_AP, &wifi_config);
    esp_wifi_start();
    ESP_LOGI(TAG, "AP WiFi démarré: SSID=%s", WIFI_SSID);
}

// =============================================================================
// INITIALISATION DU MODULE LoRa (SX1278)
// =============================================================================

static void lora_init(void)
{
    spi_bus_config_t spi_config = {
        .miso_io_num = LORA_MISO_PIN,
        .mosi_io_num = LORA_MOSI_PIN,
        .sclk_io_num = LORA_SCK_PIN,
        .quadwp_io_num = -1,
        .quadhd_io_num = -1,
        .max_transfer_sz = 256,
    };
    esp_err_t ret = spi_bus_initialize(VSPI_HOST, &spi_config, 1);
    if(ret != ESP_OK) {
        ESP_LOGE(TAG, "Erreur d'initialisation du bus SPI pour LoRa");
        return;
    }
    // Initialisez le module LoRa avec votre driver (ex. LoRa_setPins et LoRa_begin)
    ESP_LOGI(TAG, "Module LoRa initialisé à %.0f Hz", LORA_FREQUENCY);
}

// =============================================================================
// GESTION DES CAPTEURS ET DE LEUR STATUT
// =============================================================================

static bool isSensorAuthorized(uint32_t id) {
    for (int i = 0; i < numAuthorizedSensors; i++) {
        if (authorizedSensors[i] == id)
            return true;
    }
    return false;
}

static void updateAuthorizedSensor(uint32_t id, bool add) {
    if (add) {
        if (!isSensorAuthorized(id) && numAuthorizedSensors < MAX_SENSORS) {
            authorizedSensors[numAuthorizedSensors++] = id;
            ESP_LOGI(TAG, "Capteur autorisé ajouté: ID = %u", id);
        } else {
            ESP_LOGI(TAG, "Capteur ID %u déjà autorisé ou liste pleine", id);
        }
    } else {
        bool found = false;
        for (int i = 0; i < numAuthorizedSensors; i++) {
            if (authorizedSensors[i] == id) {
                for (int j = i; j < numAuthorizedSensors - 1; j++) {
                    authorizedSensors[j] = authorizedSensors[j + 1];
                }
                numAuthorizedSensors--;
                found = true;
                ESP_LOGI(TAG, "Capteur retiré: ID = %u", id);
                break;
            }
        }
        if (!found) {
            ESP_LOGI(TAG, "Capteur ID %u non trouvé dans la liste autorisée", id);
        }
    }
}

static void registerSensor(const SensorData *data) {
    if (!isSensorAuthorized(data->sensorId)) {
        ESP_LOGW(TAG, "Message reçu d'un capteur non autorisé (ID = %u) -> Ignoré", data->sensorId);
        return;
    }
    for (int i = 0; i < numSensors; i++) {
        if (sensorNodes[i].id == data->sensorId) {
            sensorNodes[i].data = *data;
            sensorNodes[i].lastUpdate = xTaskGetTickCount() * portTICK_PERIOD_MS;
            return;
        }
    }
    if (numSensors < MAX_SENSORS) {
        sensorNodes[numSensors].id = data->sensorId;
        sensorNodes[numSensors].data = *data;
        sensorNodes[numSensors].lastUpdate = xTaskGetTickCount() * portTICK_PERIOD_MS;
        numSensors++;
        ESP_LOGI(TAG, "Capteur autorisé mis en mémoire: ID = %u", data->sensorId);
    } else {
        ESP_LOGW(TAG, "Nombre maximum de capteurs enregistré atteint!");
    }
}

// =============================================================================
// FONCTIONS POUR AGGÉRER LES DONNÉES DES CAPTEURS
// =============================================================================

// Vérifie l'état des capteurs et logue ceux dont la dernière mise à jour est trop ancienne
static void check_sensor_status(void)
{
    unsigned long now = xTaskGetTickCount() * portTICK_PERIOD_MS;
    for (int i = 0; i < numSensors; i++) {
        if ((now - sensorNodes[i].lastUpdate) > DATA_TIMEOUT_MS) {
            ESP_LOGW(TAG, "Capteur ID %u : Aucune donnée depuis %lu ms (Panne ou dysfonctionnement)", 
                     sensorNodes[i].id, now - sensorNodes[i].lastUpdate);
        }
    }
}

// Calcule la moyenne des données de tous les capteurs actifs (dont la dernière mise à jour est récente)
static void aggregate_sensor_data(SensorData *avgData)
{
    unsigned long now = xTaskGetTickCount() * portTICK_PERIOD_MS;
    int count = 0;
    float sumTemp = 0.0f, sumHum = 0.0f, sumGas = 0.0f, sumWater = 0.0f;
    uint32_t sumTVOC = 0, sumECO2 = 0;
    unsigned long sumTimestamp = 0;
    
    for (int i = 0; i < numSensors; i++) {
        if ((now - sensorNodes[i].lastUpdate) <= DATA_TIMEOUT_MS) {
            sumTemp    += sensorNodes[i].data.temperature;
            sumHum     += sensorNodes[i].data.humidity;
            sumGas     += sensorNodes[i].data.gasLevel;
            sumWater   += sensorNodes[i].data.waterFlow;
            sumTVOC    += sensorNodes[i].data.tvoc;
            sumECO2    += sensorNodes[i].data.eco2;
            sumTimestamp += sensorNodes[i].data.timestamp;
            count++;
        }
    }
    if (count > 0) {
        avgData->temperature = sumTemp / count;
        avgData->humidity    = sumHum / count;
        avgData->gasLevel    = sumGas / count;
        avgData->waterFlow   = sumWater / count;
        avgData->tvoc        = sumTVOC / count;
        avgData->eco2        = sumECO2 / count;
        avgData->timestamp   = sumTimestamp / count;
    } else {
        // Aucun capteur actif : on garde les dernières données valides
        *avgData = lastValidSensorData;
    }
}

// =============================================================================
// MISE À JOUR DES PARAMÈTRES D'ÉLEVAGE
// =============================================================================

static void updateParametersForAge(void) {
    for (int i = 6; i >= 0; i--) {
        if (currentParams.ageInDays >= AGE_PARAMETERS[i].ageInDays) {
            currentParams.targetTemp = AGE_PARAMETERS[i].targetTemp;
            currentParams.tempMargin = AGE_PARAMETERS[i].tempMargin;
            currentParams.targetHumidity = AGE_PARAMETERS[i].targetHumidity;
            currentParams.humidityMargin = AGE_PARAMETERS[i].humidityMargin;
            currentParams.lightHoursPerDay = AGE_PARAMETERS[i].lightHoursPerDay;
            break;
        }
    }
}

static void updateParameters(void) {
    updateParametersForAge();
    int numConfigs = sizeof(densityConfigs) / sizeof(DensityRange);
    for (int i = 0; i < numConfigs; i++) {
        if (nombrePoulets >= densityConfigs[i].minPoulets &&
            nombrePoulets <= densityConfigs[i].maxPoulets) {
            currentParams.targetTemp = densityConfigs[i].targetTemp;
            currentParams.targetHumidity = densityConfigs[i].targetHumidity;
            currentParams.lightHoursPerDay = densityConfigs[i].lightHoursPerDay;
            break;
        }
    }
}

// =============================================================================
// TÂCHE OTA (Over-The-Air)
// =============================================================================

void ota_update_task(void *pvParameter) {
    while (1) {
        ESP_LOGI(TAG, "Vérification OTA...");
        // Implémentez ici votre procédure OTA (ex. avec esp_https_ota)
        vTaskDelay(pdMS_TO_TICKS(60000));  // Vérification toutes les minutes
    }
}

// =============================================================================
// TÂCHE DE CONTRÔLE DE L'ENVIRONNEMENT (Automatisations)
// =============================================================================

void control_environment_task(void *pvParameter) {
    while (1) {
        // D'abord, vérification de l'état des capteurs
        check_sensor_status();
        // Calcul de la moyenne des données des capteurs actifs
        aggregate_sensor_data(&sensorData);
        lastDataReceived = xTaskGetTickCount() * portTICK_PERIOD_MS;  // MàJ si on a reçu des données récentes
        
        // Utilisation de la moyenne pour le contrôle
        float tempDiff = sensorData.temperature - currentParams.targetTemp;
        if (tempDiff > currentParams.tempMargin) {
            relayData.relayStates[VENTILATION_1] = true;
            relayData.relayStates[VENTILATION_2] = (tempDiff > currentParams.tempMargin * 2);
            relayData.relayStates[CHAUFFAGE_1] = false;
            relayData.relayStates[CHAUFFAGE_2] = false;
        } else if (tempDiff < -currentParams.tempMargin) {
            relayData.relayStates[CHAUFFAGE_1] = true;
            relayData.relayStates[CHAUFFAGE_2] = (tempDiff < -currentParams.tempMargin * 2);
            relayData.relayStates[VENTILATION_1] = false;
            relayData.relayStates[VENTILATION_2] = false;
        }
        
        float humidityDiff = sensorData.humidity - currentParams.targetHumidity;
        if (humidityDiff < -currentParams.humidityMargin) {
            relayData.relayStates[BRUMISATION] = true;
        } else if (humidityDiff > currentParams.humidityMargin) {
            relayData.relayStates[BRUMISATION] = false;
            relayData.relayStates[VENTILATION_1] = true;
        }
        
        // Lecture du temps depuis DS1302 pour l'éclairage
        DS1302_Time now;
        ds1302_get_time(&now);
        int currentHour = now.hour;
        int startHour = 6;
        int lightHours = currentParams.lightHoursPerDay;
        int endHour = startHour + lightHours;
        bool lightOn = false;
        if (endHour < 24) {
            lightOn = (currentHour >= startHour && currentHour < endHour);
        } else {
            endHour = endHour - 24;
            lightOn = (currentHour >= startHour || currentHour < endHour);
        }
        relayData.relayStates[ECLAIRAGE] = lightOn;
        
        // Pompe à eau
        if (sensorData.waterFlow < 0.1f) {
            relayData.relayStates[POMPE_EAU] = true;
            lastValidSensorData = sensorData;
        }
        
        // Gestion des alarmes
        bool alarmCondition = (sensorData.gasLevel > GAS_ALARM_THRESHOLD) ||
                              (fabs(tempDiff) > TEMP_ALARM_MARGIN) ||
                              (fabs(humidityDiff) > HUMIDITY_ALARM_MARGIN) ||
                              (sensorData.tvoc > TVOC_THRESHOLD) ||
                              (sensorData.eco2 > ECO2_THRESHOLD);
        relayData.relayStates[ALARME] = alarmCondition;
        
        // Mise à jour physique des relais
        for (int i = 0; i < NUM_RELAYS; i++) {
            gpio_set_level(relayPins[i], relayData.relayStates[i] ? 1 : 0);
        }
        
        // Préparation des données combinées pour l'envoi (moyenne des capteurs)
        combinedData.sensors = sensorData;
        combinedData.relays = relayData;
        combinedData.params = currentParams;
        combinedData.nombrePoulets = nombrePoulets;
        // Ici, vous pouvez envoyer combinedData via ESP‑NOW à la HMI pour affichage
        
        lastControlUpdate = xTaskGetTickCount() * portTICK_PERIOD_MS;
        vTaskDelay(pdMS_TO_TICKS(30000));
    }
}

// =============================================================================
// TÂCHE DE RÉCEPTION DES PAQUETS LoRa
// =============================================================================

void lora_receive_task(void *pvParameter) {
    while (1) {
        // Implémentez ici la réception des paquets LoRa via SX1278.
        // Exemple : si un paquet est reçu, lisez-le dans une variable de type SensorData
        // puis appelez registerSensor(&sensorData);
        vTaskDelay(pdMS_TO_TICKS(100));
    }
}

// =============================================================================
// CALLBACK DE RÉCEPTION ESP‑NOW (WiFi en mode AP)
// =============================================================================

void espnow_recv_cb(const uint8_t *mac_addr, const uint8_t *data, int data_len) {
    if (data_len == sizeof(RelayStatus)) {
        memcpy(&relayData, data, sizeof(RelayStatus));
    } else if (data_len == sizeof(BreedingParameters)) {
        memcpy(&currentParams, data, sizeof(BreedingParameters));
        updateParameters();
    } else if (data_len == sizeof(HMIConfig)) {
        HMIConfig config;
        memcpy(&config, data, sizeof(HMIConfig));
        nombrePoulets = config.nombrePoulets;
        ESP_LOGI(TAG, "Nombre de poulets mis à jour via HMI : %d", nombrePoulets);
        updateParameters();
    } else if (data_len == sizeof(HMIClockConfig)) {
        HMIClockConfig clkConfig;
        memcpy(&clkConfig, data, sizeof(HMIClockConfig));
        DS1302_Time newTime = { clkConfig.second, clkConfig.minute, clkConfig.hour, clkConfig.day, clkConfig.month, clkConfig.year };
        ds1302_set_time(&newTime);
    } else if (data_len == sizeof(HMIResetCommand)) {
        HMIResetCommand resetCmd;
        memcpy(&resetCmd, data, sizeof(HMIResetCommand));
        if (resetCmd.command == 1) {
            currentParams.ageInDays = 0;
            ESP_LOGI(TAG, "Système réinitialisé pour nouvel arrivage de poussins");
        }
    } else if (data_len == sizeof(HMISensorAuthCommand)) {
        HMISensorAuthCommand authCmd;
        memcpy(&authCmd, data, sizeof(HMISensorAuthCommand));
        if (authCmd.command == 1)
            updateAuthorizedSensor(authCmd.sensorId, true);
        else if (authCmd.command == 0)
            updateAuthorizedSensor(authCmd.sensorId, false);
    } else if (data_len == sizeof(HMIProductionMode)) {
        HMIProductionMode modeCmd;
        memcpy(&modeCmd, data, sizeof(HMIProductionMode));
        if ((strcmp(productionMode, modeCmd.mode) != 0) && (strlen(productionMode) != 0)) {
            if (modeCmd.securityCode == 29858) {
                strncpy(productionMode, modeCmd.mode, sizeof(productionMode));
                ESP_LOGI(TAG, "Mode de production changé par sécurité à : %s", productionMode);
            } else {
                ESP_LOGW(TAG, "Code de sécurité incorrect - Mode non changé");
            }
        } else {
            strncpy(productionMode, modeCmd.mode, sizeof(productionMode));
            ESP_LOGI(TAG, "Mode de production initialisé à : %s", productionMode);
        }
    }
    // Mise à jour des sorties relais après réception
    for (int i = 0; i < NUM_RELAYS; i++) {
        gpio_set_level(relayPins[i], relayData.relayStates[i] ? 1 : 0);
    }
}

// =============================================================================
// FONCTION PRINCIPALE app_main()
// =============================================================================

void app_main(void)
{
    esp_err_t ret = nvs_flash_init();
    if(ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        nvs_flash_erase();
        nvs_flash_init();
    }
    ESP_LOGI(TAG, "Démarrage de la centrale ESP32");

    // Initialisation des GPIO des relais
    for (int i = 0; i < NUM_RELAYS; i++) {
        gpio_reset_pin(relayPins[i]);
        gpio_set_direction(relayPins[i], GPIO_MODE_OUTPUT);
        gpio_set_level(relayPins[i], 0);
    }

    // Initialisation du WiFi en mode AP pour que le HMI se connecte
    esp_netif_init();
    esp_event_loop_create_default();
    wifi_init_softap();

    // Initialisation d'ESP‑NOW (WiFi en mode AP)
    if (esp_now_init() != ESP_OK) {
        ESP_LOGE(TAG, "Erreur d'initialisation ESP‑NOW");
        return;
    }
    esp_now_register_recv_cb(espnow_recv_cb);

    // Initialisation du module LoRa
    lora_init();

    // Initialisation du DS1302 RTC
    ds1302_init();

    // Chargement des paramètres persistants via NVS (à implémenter si nécessaire)
    updateParameters();

    // Création des tâches FreeRTOS avec répartition sur les deux cœurs
    xTaskCreatePinnedToCore(control_environment_task, "ControlTask", 4096, NULL, 5, NULL, 1);
    xTaskCreatePinnedToCore(ota_update_task, "OTATask", 4096, NULL, 5, NULL, 0);
    xTaskCreatePinnedToCore(lora_receive_task, "LoRaReceiveTask", 4096, NULL, 5, NULL, 0);

    // Boucle principale (inutilisée, car toutes les fonctionnalités sont gérées par des tâches)
    while(1) {
        vTaskDelay(pdMS_TO_TICKS(1000));
    }
}