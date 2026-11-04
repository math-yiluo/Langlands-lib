# Invariant matrix coordinates detected on rational points

This module combines the accepted coordinate constructions of Worker 1228 and
the rational-matrix coordinate contribution. It reuses `rationalMatrix` from
`MatrixRepresentationRationalPoints`, which evaluates the actual representation
on a base point and transports global sections through `Γ(Spec k) ≅ k`.

`map_rationalMatrix` recovers the matrix of sections by scalar extension.
`pointMatrix_constant` computes the matrix of a constant point on any relative
scheme test. `stableCoordinates_iff_universal` says that the stability equation
for matrices `B` and `C` holds on every test exactly when it holds at the
universal point. The reverse implication pulls back the matrix equation and
uses coefficient naturality. No splitting identity for `B` and `C` is assumed.

`coordinateStabilityDefect` is the difference of the two sides of the
coordinate-stability equation, over an arbitrary commutative base ring.
`coordinateStabilityDefect_naturality` proves compatibility with every
morphism of relative scheme tests.

For a reduced group locally of finite type over an algebraically closed field,
`isStableCoordinates_of_basePoints` detects stability by vanishing of this
defect on base points. Each column of the universal defect is a morphism to
affine coefficient space. The published `hom_ext_rationalPoints` identifies
it with the zero morphism; naturality then gives vanishing on every test.
`isStableCoordinates_of_rationalMatrix` expresses the same criterion using
matrices over the ground field. It transports the rational-point equation
through the canonical global-sections isomorphism and applies the defect
criterion. The shared theorem occurs once in the combined module.

These are internal derivations from the actual representation, coefficient
space, and rational-point extensionality interfaces. No smoothness or
reducedness is imposed on a subgroup in these results. Character-space
invariance, the normal-kernel construction, and quotient existence require
their separate arguments.
