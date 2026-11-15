# Poisson summation on `𝔸^n`

Module `Langlands.Global.RankinSelberg.EqualAnalyticPoisson`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Main result `hasSum_poisson`: for a standard `ψ` and `Φ ∈ schwartzBruhat F n`,
`HasSum (fun η : F^n => Φ̂(η)) (Σ'_{ξ ∈ F^n} Φ(ξ))`, where `Φ̂ = fourierTransform F n ψ Φ` is the
Library's Fourier transform for the covolume-one measure. This is Tate's adelic Poisson formula
`Σ_ξ Φ(ξ) = Σ_η Φ̂(η)` (Tate's thesis, Theorem 4.2.1 and Lemma 4.2.4; Cogdell 2004, §2.3,
p.209), here for `𝔸^n` and any standard character.

## Provenance

Internal proof following Tate's route through Fourier analysis on the compact group `(𝔸/F)^n`.
It uses the generic Fourier inversion `hasSum_fourierCoeff` (`EqualAnalyticFourierSeries`), the
unfolding `integral_eq_integral_periodization` (`EqualAnalyticRowMeasure`), the annihilator result
`exists_eq_algebraMap_of_forall_eq_one`, and the domination results.

## Declarations

- `RatRow F n` (rational `1 × n` matrices), `RowQuotient F n = (𝔸/F)^n`, `ratRow F n C` (the
  adelic row vector of `C`), with `ratRow_add`, `ratRow_neg`, `ratRow_zero`, `ratRow_injective`,
  `algebraMap_adeles_injective`, `ratRowVec`, `ratRowVec_injective` and
  `matrixQuotientMap_ratRow_add`.
- `pairingCharacter F ψ n η X = ψ(Σ_j X_j η_j)`, with its additivity, periodicity under `F^n`,
  continuity, and dependence on `η`. `quotientCharacter` is its descent to `(𝔸/F)^n`
  (`quotientCharacter_mk`). `isCharacterFamily_quotientCharacter` shows these form a character
  family.
- `quotientCharacter_separates`: the characters separate points (by the annihilator theorem,
  coordinate by coordinate, using `singleRow`). `integral_quotientCharacter`: nontrivial
  characters have integral zero for `matrixQuotientHaar`.
- `archimedeanCoordinates_add`, `finiteCoordinates_add`, `archimedeanCoordinates_ratRow`,
  `finiteCoordinates_ratRow`, `IsRowDominated.norm_le_rpow`.
- `exists_local_periodization_bound`: for dominated `Φ` and every `X₀`, there are a neighbourhood
  `U` of `X₀` and a summable `u ≥ 0` with `‖Φ(ξ + X)‖ ≤ u ξ` for `X ∈ U`. A nonzero value forces
  `ξ` into `IntegralRows F n (d e)`, with `e` clearing the denominators of `X₀`. Archimedean
  decay plus `summable_integralRows` with exponent `n [F : ℚ] + 1` give the bound.
- `periodization F n Φ X = Σ'_ξ Φ(ξ + X)`: summable (`summable_periodization`,
  `summable_norm_periodization`), continuous for continuous dominated `Φ`
  (`continuous_periodization`, Mathlib `continuousOn_tsum`), and periodic. `quotientPeriodization`
  is its descent.
- `ratRowEquiv F n : RatRow F n ≃ rowLattice F n`; `star_addChar`: `conj ψ(z) = ψ(-z)`.
- `fourierCoeff_quotientPeriodization`: the `η`-th Fourier coefficient of the periodization is
  `Φ̂(-η)`, by `integral_eq_integral_periodization`.
- `hasSum_fourierTransform_ratRow`: Poisson summation for continuous, integrable and dominated
  `Φ` whose transform is dominated. Fourier inversion at `0`, then `η ↦ -η`.
- `hasSum_poisson`: the case `Φ ∈ schwartzBruhat F n`, by `schwartzBruhat_properties` and
  `fourierTransform_properties`.
