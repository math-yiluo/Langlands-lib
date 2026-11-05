# Ground-field rational points after extension of scalars

Worker 1574. This internal interface uses actual scheme pullbacks and actual
identity-test sections. `geometricRationalPoint` is the pullback lift of a
ground-field section to an extension field. Its two projections are the original
section composed with the base morphism and the identity of the new base.
`geometricRationalPoint_natural` proves compatibility with scheme morphisms.

`HasDenseGeometricRationalPoints k K X` means that the union of the images of
these extended ground-field sections is dense in `X_K`.
`hasDenseGeometricRationalPoints_of_denseRange` transports this property along
an actual scheme map whose scalar extension has dense image, using continuity
and the naturality identity. It does not assert that ordinary rational density
is preserved by scalar extension.

This interface is derived from the actual pullback universal property in Mathlib
and from the published identity-test `RationalPoint` convention in
`Langlands.AlgebraicGeometry.PointTopology.RationalPoints`. It is an internal
construction for the density argument in
`Langlands.GroupScheme.Rational.RationalMaximalTorusDensityReduction`.
