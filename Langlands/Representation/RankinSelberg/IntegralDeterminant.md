# Normalized determinant of an integral invertible matrix

`Langlands.RankinSelberg.normalizedAbs_det_of_mem_integralSubgroup` states that
`T.normalizedAbs (Matrix.det k.val) = 1` for an invertible `(r + 1)`-square matrix
`k` in `Conductor.integralSubgroup T.Integers r`, over any supplied p-adic field
and its topological data `T`.

This is the unchanged declaration extracted from
`WeightedWhittakerSquareReduction`. Both `det k` and `det k⁻¹` are integral, so
their normalized absolute values are at most one. Their product is one, which
forces both values to be one. The extraction lets the weighted-square and
row-slice proofs share the result without importing either analytic proof into
the other. Its original namespace and hypotheses are retained.
