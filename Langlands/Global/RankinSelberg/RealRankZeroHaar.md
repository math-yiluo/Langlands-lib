# The quotient measure on `N₁(ℝ) \ GL₁(ℝ)`

Helper module for the rank-one (`r = 0`) case of
`Langlands.Global.RankinSelbergGlobal.RealEqualFunctionalEquationStatement`. Authored by
Worker 823. All declarations are proved; there are no hypotheses or axioms.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealRankZero`. The Borel measurable structures on
`ℝˣ`, `GL₁(ℝ)`, `N₁(ℝ)` and the quotient `LeftUnipotentQuotient 0 ℝ` are local instances,
equal to the ones used by the Library's `RealQuotientMeasureData`.

## The multiplicative Haar measure `|x|⁻¹ dx`

- `invAbs x = |x|⁻¹` (as an element of `ℝ≥0`, equal to `0` at `x = 0`) and
  `invAbsVolume = |x|⁻¹ dx`, Lebesgue measure with density `invAbs`.
- `unitsHaar : Measure ℝˣ` is the pullback (`Measure.comap`) of `invAbsVolume` along the
  open embedding `Units.val : ℝˣ → ℝ`.
- `map_val_unitsHaar`: pushing `unitsHaar` forward to `ℝ` gives back `invAbsVolume`
  (the complement `{0}` of the range has measure `0`).
- `integral_unitsHaar`, `integrable_unitsHaar_iff`: for `G : ℝ → ℂ`,
  `∫ G(u) d(unitsHaar)(u) = ∫ |x|⁻¹ G(x) dx`, and integrability on `ℝˣ` is equivalent to
  integrability of `x ↦ |x|⁻¹ G(x)` on `ℝ`.
- `invAbsVolume_preimage_mul`: for `c ≠ 0`, `|x|⁻¹ dx` is invariant under `x ↦ c x`;
  proved from `Real.map_volume_mul_left` (Lebesgue measure scales by `|c|⁻¹`) and
  `|cx|⁻¹ = |c|⁻¹ |x|⁻¹`.
- `unitsHaar_isMulLeftInvariant`: left invariance of `unitsHaar`, from the previous
  lemma and `Units.val '' (g⁻¹ S) = g⁻¹ · (Units.val '' S)`.
- `unitsHaar_isHaarMeasure`: `unitsHaar` is a Haar measure. The compact set
  `unitsIcc = {u | u ∈ [1, 2]}` has nonempty interior and measure
  `∫_1^2 x⁻¹ dx ∈ (0, ∞)`, so Mathlib's `isHaarMeasure_of_isCompact_nonempty_interior`
  applies.
- `unitsSecondCountable`: `ℝˣ` is second countable (it embeds into `ℝ`); this is needed
  for Mathlib's uniqueness of Haar measures.

## Quotient measures

- `quotientUnits : LeftUnipotentQuotient 0 ℝ ≃ₜ ℝˣ` is the composition of the Library's
  `rankOneQuotientHomeomorph` (`N₁ \ GL₁ ≃ₜ GL₁`, the unipotent group being trivial) with
  the inverse of `tateScalarEquiv ℝ` (`ℝˣ ≃ GL₁(ℝ)`), so `[g] ↦ det g`
  (`quotientUnits_mk`).
- `out_eq`, `quotientUnits_symm_out`: the chosen representative `q.out` of a class is its
  image under `rankOneQuotientHomeomorph`; in particular the representative of the class
  of `u ∈ ℝˣ` is the scalar matrix `tateScalarEquiv ℝ u`.
- `quotientUnits_rightTranslate`: right translation by `g` on the quotient corresponds to
  multiplication by `det g` on `ℝˣ`.
- For `D : RealQuotientMeasureData 0`, `mapQuotientUnits_isMulLeftInvariant` and
  `mapQuotientUnits_regular`: the pushforward of `D.measure` to `ℝˣ` is left invariant
  (from the right invariance field of `D.compatible` and commutativity of `ℝˣ`) and
  regular (from the regularity field).
- `exists_measure_eq`: there is `κ ≠ 0` in `ℝ≥0` with
  `D.measure = κ • (quotientUnits.symm)_* unitsHaar`. The constant is Mathlib's
  `haarScalarFactor`, given by `isMulLeftInvariant_eq_smul`; it is nonzero since
  `D.measure ≠ 0` (the nonzero field of `D.compatible`).
- `unitsExtend H` extends a function `H` on the quotient to `ℝ` by
  `x ↦ H(quotientUnits⁻¹(x))` for `x ≠ 0` and `0` at `x = 0`.
- `integral_eq`, `integrable_iff`: if `D.measure = κ • (quotientUnits.symm)_* unitsHaar`
  (with `κ ≠ 0` for the second), then
  `∫ H dD.measure = κ ∫ |x|⁻¹ (unitsExtend H)(x) dx`, and `H` is `D.measure`-integrable
  iff `x ↦ |x|⁻¹ (unitsExtend H)(x)` is Lebesgue integrable. Proved by
  `MeasurableEmbedding.integral_map` / `integrable_map_iff` for the homeomorphism and the
  previous transfer lemmas.

## Provenance

Standard facts: `|x|⁻¹ dx` is the Haar measure of `ℝˣ` (e.g. Tate's thesis,
Cassels–Fröhlich 1967, Chapter XV, section 2.3) and Haar measures on a locally compact
group are unique up to a positive scalar. The identification of a quotient measure on
`N₁ \ GL₁` with a multiple of it is internal to this project: in rank one the quotient is
the group itself.
