# Points and actual Lie vectors of a weight vector group

This internal construction compares points of an affine vector group with its
actual Lie kernel. The field, coefficient algebras and group schemes have an
arbitrary common universe. No restriction on characteristic is imposed.

Given natural finite vector coordinates `e`, `vectorPointLieEquiv` is an
additive equivalence from the additive type tag of the coefficient-algebra
points to the additive actual Lie kernel. It sends a point's coordinates to
the tangent vector with the same epsilon coefficients using the published
`vectorAffineCoordinates` and inverse `vectorLieCoordinates`. Its inverse
uses the tangent coefficients as point coordinates. The coordinate formula
proves both inverse laws and additivity.

`vectorPointLieEquiv_naturality` proves compatibility with every map of
coefficient algebras by applying the injective Lie coordinate map and using
the naturality of the two coordinate maps.
`vectorPointLieEquiv_act` proves that an action scalar linear in these
coordinates becomes its actual differential. It is exactly the published
linear-action differential formula conjugated by the coordinate maps.
Scalar linearity is an explicit premise for this general action result.

The actual tangent point is epsilon times the constant original point in
the coordinate scalar structure. `vectorAffineCoordinates_symm_smul`
converts coefficient scalars to global-function scalars, and
`vectorPointLieEquiv_val` applies the published epsilon formula to obtain
this intrinsic description.

When the coordinates have a fixed nonzero character weight under a split
torus, `vectorPointLieEquiv_eq_of_weight` proves independence of the chosen
weight coordinates, even if their dimensions are presented differently.
The proof uses the published uniqueness of the weight scalar structure on
the dual-number test. It does not assert independence for arbitrary vector
coordinates without this weight hypothesis.

The provenance is an internal deduction from the imported vector-coordinate,
linear-action and weight-scalar-uniqueness results. This module alone does
not realize a root group, identify a Galois restriction fiber, or construct
root valuations or apartments.
