# The quotient measure on `N₁(ℂ) \ GL₁(ℂ)`

Helper module for the rank-one (`r = 0`) case of the complex equal-rank local functional
equation (the `r = 0` instance of the premise `LocalE` of
`Langlands.Global.RankinSelbergGlobal.ComplexPlaceFunctionalEquationStatement`'s
reductions). It is the complex analogue of
`Langlands.Global.RankinSelberg.RealRankZeroHaar`. All declarations are proved; there are
no hypotheses or axioms.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.ComplexRankZero`. The Borel measurable structures on
`ℂˣ`, `GL₁(ℂ)`, `N₁(ℂ)` and the quotient `LeftUnipotentQuotient 0 ℂ` are local instances,
equal to the ones used by the Library's `ComplexQuotientMeasureData`.

## The multiplicative Haar measure `|z|⁻² dz`

Here `|z|` is the usual absolute value of `z ∈ ℂ` and `dz` is Lebesgue measure on `ℂ`
(Mathlib's `volume`, transported from `ℝ²`).

- `invNormSq z = |z|⁻²` (as an element of `ℝ≥0`, equal to `0` at `z = 0`) and
  `invNormSqVolume = |z|⁻² dz`, Lebesgue measure with density `invNormSq`.
- `unitsHaar : Measure ℂˣ` is the pullback (`Measure.comap`) of `invNormSqVolume` along
  the open embedding `Units.val : ℂˣ → ℂ`.
- `range_val`, `map_val_unitsHaar`: the range of `Units.val` is `{0}ᶜ`, and pushing
  `unitsHaar` forward to `ℂ` gives back `invNormSqVolume` (the point `0` has measure `0`).
- `integral_unitsHaar`, `integrable_unitsHaar_iff`: for `G : ℂ → ℂ`,
  `∫ G(u) d(unitsHaar)(u) = ∫ |z|⁻² G(z) dz`, and integrability on `ℂˣ` is equivalent to
  integrability of `z ↦ |z|⁻² G(z)` on `ℂ`.
- `map_volume_mul_left`: for `c ≠ 0`, the image of Lebesgue measure under `z ↦ c z` is
  `|c|⁻² dz`. Multiplication by `c` is an `ℝ`-linear map of `ℂ` whose determinant is the
  algebra norm `N_{ℂ/ℝ}(c) = |c|²` (`Algebra.norm_complex_apply`), so Mathlib's
  `map_linearMap_addHaar_eq_smul_addHaar` applies.
- `invNormSqVolume_preimage_mul`: for `c ≠ 0`, `|z|⁻² dz` is invariant under `z ↦ c z`;
  proved from the previous lemma and `|cz|⁻² = |c|⁻² |z|⁻²`.
- `unitsHaar_apply`, `image_val_preimage_mul`, `unitsHaar_isMulLeftInvariant`: left
  invariance of `unitsHaar`, from the previous lemma and
  `Units.val '' (g⁻¹ S) = g⁻¹ · (Units.val '' S)`.
- `unitsHaar_isHaarMeasure`: `unitsHaar` is a Haar measure. The units with absolute value
  in `[1, 2]` (`unitsAnnulus`, the preimage of the closed annulus `closedAnnulus`) form a
  compact set whose interior contains `3/2` (it contains the preimage of the open annulus
  `openAnnulus`). Its measure is positive, since the open annulus has positive Lebesgue
  measure and the density is positive there, and finite, since the density is at most `1`
  on the annulus, which is compact. Mathlib's
  `isHaarMeasure_of_isCompact_nonempty_interior` then applies.
- `unitsSecondCountable`: `ℂˣ` is second countable (it embeds into `ℂ`); this is needed
  for Mathlib's uniqueness of Haar measures.

## Quotient measures

- `quotientUnits : LeftUnipotentQuotient 0 ℂ ≃ₜ ℂˣ` is the composition of the Library's
  `rankOneQuotientHomeomorph` (`N₁ \ GL₁ ≃ₜ GL₁`, the unipotent group being trivial) with
  the inverse of `tateScalarEquiv ℂ` (`ℂˣ ≃ GL₁(ℂ)`), so `[g] ↦ det g`
  (`quotientUnits_mk`).
- `out_eq`, `quotientUnits_symm_out`: the chosen representative `q.out` of a class is its
  image under `rankOneQuotientHomeomorph`; in particular the representative of the class
  of `u ∈ ℂˣ` is the scalar matrix `tateScalarEquiv ℂ u`.
- `quotientUnits_rightTranslate`: right translation by `g` on the quotient corresponds to
  multiplication by `det g` on `ℂˣ`.
- For `D : ComplexQuotientMeasureData 0`, `mapQuotientUnits_isMulLeftInvariant` and
  `mapQuotientUnits_regular`: the pushforward of `D.measure` to `ℂˣ` is left invariant
  (from the right invariance field of `D.compatible` and commutativity of `ℂˣ`) and
  regular (from the regularity field).
- `exists_measure_eq`: there is `κ ≠ 0` in `ℝ≥0` with
  `D.measure = κ • (quotientUnits.symm)_* unitsHaar`. The constant is Mathlib's
  `haarScalarFactor`, given by `isMulLeftInvariant_eq_smul`; it is nonzero since
  `D.measure ≠ 0` (the nonzero field of `D.compatible`).
- `unitsExtend H` extends a function `H` on the quotient to `ℂ` by
  `z ↦ H(quotientUnits⁻¹(z))` for `z ≠ 0` and `0` at `z = 0`; `unitsExtend_val` records
  its value at a unit.
- `integral_eq`, `integrable_iff`: if `D.measure = κ • (quotientUnits.symm)_* unitsHaar`
  (with `κ ≠ 0` for the second), then
  `∫ H dD.measure = κ ∫ |z|⁻² (unitsExtend H)(z) dz`, and `H` is `D.measure`-integrable
  iff `z ↦ |z|⁻² (unitsExtend H)(z)` is Lebesgue integrable. Proved by
  `MeasurableEmbedding.integral_map` / `integrable_map_iff` for the homeomorphism and the
  previous transfer lemmas.

## Provenance

Standard facts: `|z|⁻² dz` is a Haar measure of `ℂˣ` (e.g. Tate's thesis,
Cassels–Fröhlich 1967, Chapter XV, section 2.3, where the normalized absolute value on
`ℂ` is `|z|²`) and Haar measures on a locally compact group are unique up to a positive
scalar. The identification of a quotient measure on `N₁ \ GL₁` with a multiple of it is
internal to this project: in rank one the quotient is the group itself. The module follows
the structure of the real-place module `RealRankZeroHaar`.
