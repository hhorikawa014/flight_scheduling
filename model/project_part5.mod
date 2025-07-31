# sets
set FLIGHT = 1..40 by 1;
set CAPTAIN = 1..16 by 1;
set FO = 1..16 by 1;
set PORT = 1..5 by 1;

# parameters
param captain_cost {FLIGHT, CAPTAIN};
param fo_cost {FLIGHT, FO};
param captain_initial_location {CAPTAIN};
param fo_initial_location {FO};
param origin {FLIGHT};
param destination {FLIGHT};
param departure_time {FLIGHT};
param arrival_time {FLIGHT};
param downtime := 60;
param faa_regulation_time := 480;

# valid sets
set VALID_CAPTAIN_INIT = {f in FLIGHT, c in CAPTAIN: captain_initial_location[c] = origin[f]};
set VALID_FO_INIT = {f in FLIGHT, fo in FO: fo_initial_location[fo] = origin[f]};
set VALID_CAPTAIN_TRANSIT = {k in FLIGHT, m in FLIGHT, c in CAPTAIN: m>k and destination[k] = origin[m] and arrival_time[k]+downtime <= departure_time[m]};
set VALID_FO_TRANSIT = {k in FLIGHT, m in FLIGHT, fo in FO: m>k and destination[k] = origin[m] and arrival_time[k]+downtime <= departure_time[m]};
set VALID_CAPTAIN_FINAL = {f in FLIGHT, c in CAPTAIN: destination[f] = captain_initial_location[c]};  # added
set VALID_FO_FINAL = {f in FLIGHT, fo in FO: destination[f] = fo_initial_location[fo]};  # added

# decision variables
var X_cap {f in FLIGHT, c in CAPTAIN} binary;
var X_fo {f in FLIGHT, fo in FO} binary;
var S_cap {f in FLIGHT, c in CAPTAIN} binary;
var S_fo {f in FLIGHT, fo in FO} binary;
var L_cap {f in FLIGHT, c in CAPTAIN} binary;
var L_fo {f in FLIGHT, fo in FO} binary;
var Z_cap {(k,m,c) in VALID_CAPTAIN_TRANSIT} binary;
var Z_fo {(k,m,c) in VALID_FO_TRANSIT} binary;
var ST_cap {c in CAPTAIN} integer;
var ST_fo {fo in FO} integer;
var ET_cap {c in CAPTAIN} integer;
var ET_fo {fo in FO} integer;

# formulation
minimize total_cost: sum {f in FLIGHT, c in CAPTAIN} (X_cap[f,c] * captain_cost[f,c]) + sum {f in FLIGHT, fo in FO} (X_fo[f,fo] * fo_cost[f,fo]);

subject to
one_flight_one_cap {f in FLIGHT}: sum {c in CAPTAIN} X_cap[f,c] = 1;
one_flight_one_fo {f in FLIGHT}: sum {fo in FO} X_fo[f,fo] = 1;

one_init_flight_cap {c in CAPTAIN}: sum {f in FLIGHT} S_cap[f,c] = 1;
one_init_flight_fo {fo in FO}: sum {f in FLIGHT} S_fo[f,fo] = 1;

x_always_ulim_s_cap {(f,c) in VALID_CAPTAIN_INIT}: S_cap[f,c] <= X_cap[f,c];
x_always_ulim_s_fo {(f,fo) in VALID_FO_INIT}: S_fo[f,fo] <= X_fo[f,fo];

init_flight_first_cap {(m,c) in VALID_CAPTAIN_INIT, k in FLIGHT: m>k}: X_cap[k,c] <= 1-S_cap[m,c];
init_flight_first_fo {(m,fo) in VALID_FO_INIT, k in FLIGHT: m>k}: X_fo[k,fo] <= 1-S_fo[m,fo];

valid_init_departure_cap {f in FLIGHT, c in CAPTAIN: not (f,c) in VALID_CAPTAIN_INIT}: S_cap[f,c] = 0;
valid_init_departure_fo {f in FLIGHT, fo in FO: not (f,fo) in VALID_FO_INIT}: S_fo[f,fo] = 0;

transit_limit1_cap {k in FLIGHT, c in CAPTAIN}: sum {m in FLIGHT: (k,m,c) in VALID_CAPTAIN_TRANSIT} Z_cap[k,m,c] <= X_cap[k,c];
transit_limit2_cap {m in FLIGHT, c in CAPTAIN}: sum {k in FLIGHT: (k,m,c) in VALID_CAPTAIN_TRANSIT} Z_cap[k,m,c]+S_cap[m,c] >= X_cap[m,c];
transit_limit1_fo {k in FLIGHT, fo in FO}: sum {m in FLIGHT: (k,m,fo) in VALID_FO_TRANSIT} Z_fo[k,m,fo] <= X_fo[k,fo];
transit_limit2_fo {m in FLIGHT, fo in FO}: sum {k in FLIGHT: (k,m,fo) in VALID_FO_TRANSIT} Z_fo[k,m,fo]+S_fo[m,fo] >= X_fo[m,fo];

z_enforce_k_cap {(k,m,c) in VALID_CAPTAIN_TRANSIT}: Z_cap[k,m,c] <= X_cap[k,c];
z_enforce_m_cap {(k,m,c) in VALID_CAPTAIN_TRANSIT}: Z_cap[k,m,c] <= X_cap[m,c];
z_enforce_k_fo {(k,m,fo) in VALID_FO_TRANSIT}: Z_fo[k,m,fo] <= X_fo[k,fo];
z_enforce_m_fo {(k,m,fo) in VALID_FO_TRANSIT}: Z_fo[k,m,fo] <= X_fo[m,fo];

def_last_flight_cap {k in FLIGHT, c in CAPTAIN}: L_cap[k,c] = X_cap[k,c] - sum {m in FLIGHT: (k,m,c) in VALID_CAPTAIN_TRANSIT} Z_cap[k,m,c];
def_last_flight_fo {k in FLIGHT, fo in FO}: L_fo[k,fo] = X_fo[k,fo] - sum {m in FLIGHT: (k,m,fo) in VALID_FO_TRANSIT} Z_fo[k,m,fo];

def_st_cap {c in CAPTAIN}: ST_cap[c] = sum {(f,c) in VALID_CAPTAIN_INIT} (S_cap[f,c]*departure_time[f]);  # linear since departure_time is a parameter
def_st_fo {fo in FO}: ST_fo[fo] = sum {(f,fo) in VALID_FO_INIT} (S_fo[f,fo]*departure_time[f]);  # linear since departure_time is a parameter

def_et_cap {c in CAPTAIN}: ET_cap[c] = sum {f in FLIGHT} (L_cap[f,c]*arrival_time[f]);  # linear since arrival_time is a parameter
def_et_fo {fo in FO}: ET_fo[fo] = sum {f in FLIGHT} (L_fo[f,fo]*arrival_time[f]);  # linear since arrival_time is a parameter

faa_regulation_cap {c in CAPTAIN}: ET_cap[c] - ST_cap[c] <= faa_regulation_time;
faa_regulation_fo {fo in FO}: ET_fo[fo] - ST_fo[fo] <= faa_regulation_time;

# added
return_to_init_cap {c in CAPTAIN}: sum {(f,c) in VALID_CAPTAIN_FINAL} L_cap[f,c] = 1;
return_to_init_fo {fo in FO}: sum {(f,fo) in VALID_FO_FINAL} L_fo[f,fo] = 1;
