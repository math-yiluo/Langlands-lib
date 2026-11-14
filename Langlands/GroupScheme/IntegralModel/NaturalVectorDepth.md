# Actual depth models from natural vector coordinates

This derived module transports the integer-depth vector family along an actual
isomorphism from a generic group to a finite-dimensional standard vector group.
The integral polynomial group remains unchanged; only its generic-fibre
identification is composed with the inverse isomorphism. Consequently the model
is smooth with geometrically connected fibres, and its integral points are
exactly those generic points whose vector coordinates lie in the specified
valuation ball. Ordered depths admit an actual model map extending the generic
identity, and every such extension has a smooth, connected and unipotent actual
special-fibre kernel.

For a Henselian integer-valued valuation, the normalized additive value from the
existing prolongation API has the threshold `r` exactly when the multiplicative
value is at most `exp(-ceil(r))`. At zero both sides hold; at nonzero elements
this is the base value formula `-log(v(x))` and the integer ceiling adjunction.
Taking the finite minimum gives the exact additive coordinate threshold, also
in dimension zero, when the minimum is infinite.

The definition `naturalVectorDepthModel` applies this transport to the actual
vector-group isomorphism supplied by natural group coordinates on every scheme
test. The coordinate formula proves that the generic point coordinates of the
model are precisely the supplied global-section coordinates, evaluated by the
canonical global-sections identification for the field. These are actual scheme
isomorphisms and point images, rather than rational-point-only identifications.

The kernel proof uses generic rigidity to identify every compatible extension
with the transported explicit transition, and then reuses the integer-depth
vector kernel computation. Henselianity is needed only for the chosen additive
valuation API, not for the model construction or the kernel theorem.

The provenance is internal transport and valuation algebra. Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Section C.2, printed pp.697–698 /
PDF pp.728–729, motivates the scaled additive models. No assertion identifies
an arbitrary supplied Bruhat–Tits root filtration with the constructed balls.
For root groups without higher roots, the existing all-test weight-coordinate
existence theorem supplies the required natural coordinate input; identification
with the supplied apartment valuation remains a separate obligation.
