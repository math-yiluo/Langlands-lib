# The normalized Haar measure of the radical in matrix coordinates

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingRadicalHaar` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) compares two Haar measures on the radical
`U'(𝔸) ≅ M_((t+1) × (r+1))(𝔸)`. The first is `haarN`, normalized so that the quotient by the
rational radical lattice has mass one. The second is the unnormalized Haar measure
`openCellHaar` of [CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md), with
which `openCellIntegral` is defined. Their ratio is the constant `κ` of
`CuspidalPairEisensteinUnfoldingStatement`.

## Contents

- Local instances: the Borel σ-algebra on `M_((t+1) × (r+1))(𝔸)`, which is locally compact,
  second countable and Hausdorff. The σ-algebra is the one in the definition of
  `openCellHaar`.
- `radicalCoord F r t : Radical F r t ≃ₜ M_((t+1) × (r+1))(𝔸)`, the additive coordinates
  `Multiplicative.toAdd` (`radicalCoord_apply`).
- `openCellHaar_isAddHaarMeasure`: `openCellHaar` is an additive Haar measure (it is Mathlib's
  `Measure.addHaar`).
- `haarN_fundamentalDomain`: `haarN` gives mass one to the Library's fundamental domain of the
  radical lattice.
- `exists_map_radicalCoord_haarN` (**comparison of the radical Haar measures**): there is a
  real `κ > 0` (in `ℝ≥0`) with `haarN.map radicalCoord = κ • openCellHaar`. The image measure
  is translation invariant, because `ofAdd a * ·` corresponds to `a + ·` and `haarN` is left
  invariant. It is finite on compact sets. Mathlib's uniqueness of Haar measure
  (`Measure.isAddLeftInvariant_eq_smul`) gives `κ = addHaarScalarFactor`. If `κ` were zero,
  `haarN` would vanish, contradicting `haarN_fundamentalDomain`.
- `integral_haarN_eq`: if `κ ∈ ℝ≥0` satisfies `haarN.map radicalCoord = κ • openCellHaar`,
  then for every `G : M_((t+1) × (r+1))(𝔸) → ℂ`,
  `∫ G(Y.toAdd) dhaarN(Y) = κ ∫ G dopenCellHaar`, by `MeasurableEmbedding.integral_map`.
