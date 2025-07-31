# sets
# in this implementation, flight number and airplane number are both indexed
set FLIGHT = 1 .. 40 by 1;
set AIRPLANE = 1 .. 12 by 1;

# parameters
param revenue {FLIGHT, AIRPLANE};
param cost {FLIGHT, AIRPLANE};
param leasing_revenue {AIRPLANE};
param initial_location {AIRPLANE};
param origin {FLIGHT};
param destination {FLIGHT};
param departure_time {FLIGHT};
param arrival_time {FLIGHT};

param downtime := 60;
param M1 := 40;

set VALID_INIT = {f in FLIGHT, a in AIRPLANE: initial_location[a] = origin[f]};
set VALID_TRANSIT = {k in FLIGHT, m in FLIGHT: m>k and destination[k] = origin[m] and arrival_time[k]+downtime <= departure_time[m]};
set VALID_FINAL = {f in FLIGHT, a in AIRPLANE: initial_location[a] = destination[f]};  # added

# decision variables
var X {f in FLIGHT, a in AIRPLANE} binary;
var Y {a in AIRPLANE} binary;
var S {f in FLIGHT, a in AIRPLANE} binary;
var Z {(k,m) in VALID_TRANSIT, a in AIRPLANE} binary;
var L {f in FLIGHT, a in AIRPLANE} binary;  # final (last) flight of each airplane

# formulation
maximize profit: sum {f in FLIGHT, a in AIRPLANE} (revenue[f,a]-cost[f,a])*X[f,a] + sum {a in AIRPLANE} (leasing_revenue[a]*Y[a]);

subject to
one_a_per_f {f in FLIGHT}: sum {a in AIRPLANE} X[f,a] = 1;
a_assigned_or_leased_llim {a in AIRPLANE}: 1-Y[a] <= sum {f in FLIGHT} X[f,a];
a_aasigned_or_leased_ulim {a in AIRPLANE}: sum {f in FLIGHT} X[f,a] <= M1*(1-Y[a]);
init_flight_limit {(f,a) in VALID_INIT}: S[f,a] <= X[f,a];
init_flight_max {a in AIRPLANE}: sum {(f,a) in VALID_INIT} S[f,a] <= 1;
init_flight_first {(m,a) in VALID_INIT, k in FLIGHT: m>k}: X[k,a] <= 1-S[m,a];
init_flight_Y_Connection {a in AIRPLANE}: sum {(f,a) in VALID_INIT} S[f,a] = 1-Y[a];
valid_initial_departure {f in FLIGHT, a in AIRPLANE: not (f,a) in VALID_INIT}: S[f,a] = 0;
transit_limit1 {k in FLIGHT, a in AIRPLANE}: sum {m in FLIGHT: (k,m) in VALID_TRANSIT} Z[k,m,a] <= X[k,a];
transit_limit2 {m in FLIGHT, a in AIRPLANE}: sum {k in FLIGHT: (k,m) in VALID_TRANSIT} Z[k,m,a]+S[m,a] >= X[m,a];
z_enforce_k {k in FLIGHT, m in FLIGHT, a in AIRPLANE: (k,m) in VALID_TRANSIT}: Z[k,m,a] <= X[k,a];
z_enforce_m {k in FLIGHT, m in FLIGHT, a in AIRPLANE: (k,m) in VALID_TRANSIT}: Z[k,m,a] <= X[m,a];
# added
final_flight {k in FLIGHT, a in AIRPLANE}: L[k,a] = X[k,a]-sum {m in FLIGHT: (k,m) in VALID_TRANSIT} Z[k,m,a];
return_to_init {a in AIRPLANE}: sum {(f,a) in VALID_FINAL} L[f,a] = 1-Y[a];