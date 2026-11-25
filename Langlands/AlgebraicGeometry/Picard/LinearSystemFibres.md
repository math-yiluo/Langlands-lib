# Zero loci of linear-system sections with unit ideal of values

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `eq_zero_of_zeroIdeal_eq_bot`: a section with zero ideal `⊥` is zero.
- `homEquivSections_zero`, `homEquivSections_eq_zero_iff`: `σ_u = 0` iff `u = 0`.
- `bcMap K ψ` (in `BaseChangeMaps`), `pullbackSection_homEquivSections_ne_zero`: if the values of
  `v : Q → B` generate the unit ideal, then `σ_v` does not vanish on any fibre `X_B ×_B Spec K`
  over a field `K`.
- `homEquivSections_regular_and_relativeEffective` (`B` noetherian, `π` proper, flat, geometrically
  integral): then `σ_v` is a regular section and its zero ideal is a relative effective Cartier
  ideal over `Spec B` (`FibreRegularSection.isRegularSection_and_isRelativeEffectiveCartierIdeal`).

## Source

Kleiman, *The Picard scheme*, p.26 (proof of Theorem 3.13, second half): a surjection
`u : Q_T → N` gives a section `σ` with `σ_t ≠ 0` on every fibre, hence regular since the fibres are
integral, and `D = Z(σ)` is a relative effective divisor by Lemma 3.4.
