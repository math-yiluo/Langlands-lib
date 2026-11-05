# Canonical topology on rational extension of scalars

This internal construction bundles the published actual pullback comparison
`GaloisPointComparison.baseChangeCoeffEquiv k L G` as a continuous multiplicative
equivalence. Here `k → L` is any field extension, `G` is affine over `k`, and `L`
is a topological ring. The rational points of the actual base change carry
exactly `rationalPointTopology L (baseChanged k L G).X`; the coefficient points
of `G` carry the existing regular-function evaluation topology.

The algebraic comparison is identified by its first pullback projection with
`affinePointsBaseChangeMulEquiv`, following the identity-test transport
`rationalPointEquiv`. The construction composes the already published
`rationalPointsAffineHomeomorph` with the inverse of
`affinePointsBaseChangeContinuousMulEquiv`. Thus the continuous equivalence has
precisely `baseChangeCoeffEquiv` as its underlying multiplicative equivalence.

`continuous_rationalExtend` assumes a topology on `k` and continuity of its field
inclusion into `L`. It composes the rational/coefficient homeomorphism, the
published continuous coefficient-point map, and the inverse of the constructed
continuous base-change comparison. Its underlying map is the existing
`rationalExtend`, with no finite-degree, separability, completeness, or local-field
assumption. This module does not assert that a particular valuation-field
inclusion is continuous; that is a separate application.

The provenance is internal: these are topology and carrier adapters for the
existing Library constructions in `GaloisPointRational`, `Rational.PointTopology`
and `AffinePointBaseChangeSmooth`, needed to descend openness of the actual KP
zero subgroup. No new source theorem is claimed.
