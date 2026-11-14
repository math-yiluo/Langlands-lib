# Scaled integral vector-group models

This internal construction uses the polynomial vector group over an integral
domain `R` as a model of the vector group over its fraction field `K`.
Its generic-fibre identification is the canonical base-change isomorphism
followed by scaling all coordinates by a specified `t : Kˣ`. The structural
map is smooth and geometrically connected, since it is affine space.

For scaling factors `s,t` and a coefficient `c : R` with
`algebraMap R K c * t = s`, multiplication by `c` defines a compatible model
homomorphism extending the generic identity. Generic rigidity identifies
every compatible extension with this scalar map. Over a local `R`, its actual
special-fibre kernel is smooth, connected and unipotent by the vector-scalar
specialization calculation.

These are internal consequences of polynomial vector-group coordinates,
base change, generic rigidity and actual scheme kernels. In dimension one
they implement the scaled additive models used in Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Section C.2 and Fact C.2.1,
printed pp.697–698 / PDF pp.728–729, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. They do not yet identify an
arbitrary supplied root filtration with a scaled lattice.
