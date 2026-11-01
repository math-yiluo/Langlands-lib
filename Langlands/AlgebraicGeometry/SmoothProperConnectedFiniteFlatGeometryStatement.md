# Geometry and native rank before the polarized degree calculation

`Langlands.AlgebraicGeometry.SmoothProperConnectedFiniteFlatGeometryStatement`
states a preparation result over an arbitrary field, in every universe. An
actual scheme over `Spec K` is smooth of specified relative dimension `g`,
proper, and geometrically connected. For any actual finite flat
over-endomorphism, the conclusion is that the scheme is integral, its
topological Krull dimension equals `g`, the endomorphism is surjective, and
its native `Scheme.Hom.finrank` is constant and positive at every target
point.

This is a derived interface grouping consequences of existing Library
geometry. Integrality is supplied by
`Langlands.AbelianScheme.smoothGeometricIntegrality` and Mathlib's
geometric-integrality comparison over a field. The dimension combines
`Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim` with
`fieldSmoothClosedPointStalkDimension`: a closed point exists by compactness,
and its stalk dimension is a lower bound for the space dimension.
Surjectivity follows from
`finiteIrreducibleEndomorphismSurjective`. Mathlib's local constancy and
positivity results for the actual finite flat morphism then give the rank
conclusions.

The definition itself proves none of these assertions. It supplies no
polarization, numerical degree, intersection invariant, or equality of the
rank with a tensor-power exponent. Those are separate obligations of
`Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankStatement`.
