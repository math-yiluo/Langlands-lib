# Normalized absolute value of supplied local-field data: topology

`Langlands.AllField.LocalField.Foundation` proves, for an arbitrary field `F` with bundled
nonarchimedean local-field data `T : LocalFieldData F` (any characteristic), the laws of
`T.normalizedAbs` and of the supplied topology that the all-field port of the p-adic JPSS
proof uses. They replace the p-adic lemmas of `Langlands.LocalField.Normalization.Proof`
and `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` (topology of `PadicField p`).
All declarations are in namespace `Langlands.LocalFieldData`.

## Declarations

- `normalizedAbs_eq_zero_iff`: `T.normalizedAbs x = 0 ↔ x = 0`.
- `normalizedAbs_le_one_iff_mem_integers`: `T.normalizedAbs x ≤ 1 ↔ x ∈ T.Integers`.
- `normalizedAbs_lt_zpow_iff`: `T.normalizedAbs x < q ^ m ↔ T.discreteValuation x < exp m`,
  with `q = T.residueCardinality`.
- `normalizedAbs_neg`, `normalizedAbs_sub_le`: `|-x| = |x|` and the ultrametric bound
  `|x - y| ≤ max |x| |y|`.
- `hasBasis_nhds_normalizedAbs`, `normalizedAbs_balls_basis`: the balls
  `{y | |y - a| < ε}` form a neighbourhood basis at `a`, resp. a basis of the topology
  `T.topology`.
- `continuous_normalizedAbs`: `T.normalizedAbs` is continuous for `T.topology`.
- `fieldT2`, `sigmaCompactSpace`, `secondCountableTopology`, `pseudoMetrizableSpace`:
  the topology `T.topology` is Hausdorff, σ-compact, second countable and
  pseudometrizable.
- `isCompact_integers`, `isOpen_integers`: the valuation ring `T.Integers` is compact
  and open.
- `haarMeasure_regular`: every additive Haar measure on `F` for the Borel σ-algebra of
  `T.topology` is regular.

## Proof

The arithmetic laws unfold `T.normalizedAbs` through the discrete valuation and the
order isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`. The neighbourhood
basis comes from the valuation-ball basis of the valuative topology (`IsValuativeTopology`)
translated through `normalizedAbs_lt_zpow_iff`. The topological properties are the
general local-field results `Langlands.HarmonicAnalysis.GeneralLocalField.*` and Mathlib's
`IsNonarchimedeanLocalField` API, instantiated at the instances of `T`.
