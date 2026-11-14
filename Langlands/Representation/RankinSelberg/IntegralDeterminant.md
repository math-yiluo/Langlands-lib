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

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
