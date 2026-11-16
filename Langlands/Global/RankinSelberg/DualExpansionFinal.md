# The dual expansion `E'` from `J` and the dual Whittaker expansion

Module `Langlands.Global.RankinSelberg.DualExpansionFinal`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: derived. Cogdell 2004 (source `cogdell-2004-analytic-theory-gln`), §2.2, printed p.207 (PDF p.210) states the dual unfolding, in which the dual integral unfolds into
rectangle integrals of the dual Whittaker function, with an extra unipotent integration that is
the remnant of `P̃`. The implemented proof is internal: an induction on the size of the
rectangle (modules `DualExpansionPeriodStep`, `DualExpansionRectStep`), a group-theoretic
identification of the coefficient along `Y_(n,m)` (`DualExpansionRadical`, `DualExpansionConj`,
`DualExpansionBridge`) and an unfolding of the rectangle measure (`DualExpansionRectMeasure`,
`DualExpansionUnfold`).

## Geometry

- `unfoldingWeyl_eq_wPoint`: the Library's `unfoldingWeyl F h` is `wPoint` for `r = t + 1 + k`.
- `wPoint_mul_pad`: `w` commutes with `diag(g, I)`.
- `rectangularPoint_one`: `rect(1, x) = x̂` (as an `xcPoint`, with the index cast
  `t + 1 + k - (t + 1) = k`); `rectangularPoint_one_mul_pad`: `rect(1, x) · diag(g, I) =
  rect(g, x g)`; `pad_eq_rectangularPoint`.

## The dual Whittaker function

- `continuous_cuspWhittaker'`: the Library's `cuspWhittaker` is continuous (an integral over the
  compact quotient `N(F) \ N(𝔸)` of a jointly continuous integrand).
- `dualData_dualCuspWhittaker`: under the Library's `DualCuspidalWhittakerExpansion F T`, the dual
  Whittaker function `W̃ = dualFunction (cuspWhittaker F T ψ v)` is a `DualData` function
  (equivariance from the Library's `dualCuspWhittaker_unipotent_mul` with `ψ⁻¹`), and
  `cornerSum_dualCuspWhittaker` identifies its corner sum with the dual cusp form.

## Measures

- `integral_rect_cast`, `integrable_rect_cast`: transport along an equality `K₁ = K₂` of
  rectangle sizes.
- `integral_rect_mul_right`, `integrable_rect_mul_right_iff`: from
  `RectangleMeasureModulusStatement` (`J`), `∫ Ψ(x g) dx = |det g|^(-k) ∫ Ψ(x) dx`.
- `integral_rectIntegrand_eq`, `dualRectIntegral_cosetRep`: the terms of the unfolded side and of
  `E'` as rectangle integrals of `W̃(diag(b, I) · rect(g, x) · w)`.
- `detPower_neg_half`, `exists_addChar_ne_one`.

## The theorem

**`dualProjectionWhittakerExpansion_of_dualCuspidalWhittakerExpansion`**: assuming
`RectangleMeasureModulusStatement.{u}`, for every `t < r` and every actual cuspidal realization
`T` of rank `r` with `DualCuspidalWhittakerExpansion F T`, the premise
`DualProjectionWhittakerExpansion F h T` holds: for every standard `ψ`, vector `v` and
`g ∈ GL_(t+1)(𝔸)`, `x ↦ W̃(rect(g, x) w')` is integrable for `rectangleMeasure`, and
`Σ_(q ∈ N_m(F) \ GL_m(F)) |det g|^(-k/2) ∫ W̃(rect(γ_q g, x) w') dx` converges unconditionally
to the dual projection of `φ̃` at `diag(g, 1)` (here `k = r - (t + 1)`, `m = t + 1`).

Proof: write `r = t + 1 + k`. The dual projection is `|det g|^(k/2)` times the coefficient along
`Y_(n,t+1)` of `φ̃ ∘ ι` at `diag(ᵗg⁻¹, I)`. By `cornerSum_dualCuspWhittaker` and
`DualData.coefficient_eq_dualPeriod` this is the dual period of `W̃` at `w · diag(g, I)`, which
equals `dualRectT` by `dualPeriod_eq_dualRectT` and unfolds by
`DualData.hasSum_integral_rectIntegrand`. Each unfolded term is `|det g|^(-k)` times the integral
appearing in the corresponding term of `E'` (`integral_rectIntegrand_eq`, which uses `J`, and
`dualRectIntegral_cosetRep`), and the coset index sets are matched by the Library's
`rationalCosetIndexEquiv`. Integrability follows from the integrability of the term for the
trivial coset and `J`.
