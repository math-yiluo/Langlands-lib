# Smoothness of the actual general linear group scheme

Authors: Worker 57 and Worker 405. Worker 57 supplied the Lean proof; Worker 405
checked the published dependencies, exact target and universe parameters, and
prepared the proof for submission.

`Langlands.GroupScheme.GeneralLinear.smoothStatement` proves the published
proposition `Langlands.GroupScheme.GeneralLinear.SmoothStatement`. For every
small finite matrix index type `n : Type` with decidable equality and every
commutative ring object `R : CommRingCat.{u}`, the structure morphism of the
existing `groupScheme n R` is smooth. The base-ring universe `u` is arbitrary.
There are no field, characteristic, nontrivial-ring or positive-rank assumptions;
the result includes the empty matrix index and the zero ring.

The helper `coordinateRing_smooth` proves that the existing two-matrix coordinate
quotient `CoordinateRing n R` is a smooth algebra over `R`. First, the polynomial
ring `MatrixPolynomial n R = MvPolynomial (n × n) R` is formally smooth and
finitely presented, since the index type is finite. These two instances construct
its `Algebra.Smooth` instance. `Algebra.Smooth.of_isLocalization_Away` makes
`DeterminantLocalization n R` smooth over this polynomial ring, and
`Algebra.Smooth.comp` gives smoothness over `R`. The published algebra equivalence
`determinantLocalizationEquiv n R` identifies the original coordinate quotient
with this localization. `Algebra.Smooth.of_equiv` applied to its inverse
transports smoothness to the original coordinate ring.

For the closing theorem, the actual group-scheme structure map unfolds to
`Spec.map` of the algebra map from `R` to `CoordinateRing n R`.
`HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap` reduce scheme
smoothness to the helper's algebraic smoothness assertion. The theorem has the
exact target as its type, with no additional arguments or hypotheses.

This is an internal derivation from the published general linear group scheme,
its determinant-localization comparison, and Mathlib's smoothness and affine
spectrum APIs. Both project dependencies are imported by their Lean module
names. The result establishes smoothness of this group scheme and makes no
claim about reductivity or Harris Shimura scheme constructions.
