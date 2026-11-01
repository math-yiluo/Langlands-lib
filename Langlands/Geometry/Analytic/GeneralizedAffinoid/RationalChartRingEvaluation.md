# Contractive ring evaluation of weighted rational charts

This internal construction combines the published intrinsic relative rational
evaluation with its isometric comparison to scalar rational presentations. It
does not assume a scalar extension tower or any rational descent assertion.

For a rational chart `d` over a complete ultrametric field `K`, a contractive
bounded ring map `φ : A → B` into a complete ultrametric normed commutative ring,
and a tuple `b` satisfying the coordinate bounds and rational equations,
`d.ringEvaluate` is a contractive bounded ring map from the actual scalar chart
quotient to `B`. It sends each structural coefficient to its `φ` image and each
fraction coordinate to the specified tuple entry.

The proof induces a normed `K`-algebra structure on `B` through `φ`. Contractivity
and the actual source quotient bound `‖1‖ ≤ 1` prove the scalar norm inequality
and the corresponding bound for the target unit. The coordinate bounds then
give the weighted monomial bounds, including the empty monomial. Relative
evaluation descends through the actual closed rational ideal, and composition
with the isometric relative comparison gives the stated scalar quotient map.

`ringHom_ext_over_base` says that two bounded ring maps from the chart to a
normed commutative ring are equal if both restrict to the same contractive
coefficient map. Completeness and ultrametricity of the target are unnecessary
for this uniqueness assertion. The proof installs the same induced scalar
action, checks that the maps preserve it using their base equations, and applies
the published uniqueness theorem for bounded algebra maps. Unit generation
makes the denominator invertible and determines the fractions from the base.

The construction permits independent coefficient and target universes, arbitrary
positive radii, empty coordinate tuples, and zero quotient rings.
