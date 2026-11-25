# Standard additive characters of `𝔸 / F`

Module `Langlands.Global.RankinSelberg.EqualAnalyticCharacter`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

A supporting module of the harmonic analysis for the proof of `EqualAnalyticStatement`. Its main
results are:

- `exists_eq_standardCharacter_mul`: every `ψ` with `IsStandardAdditiveCharacter F ψ` is
  `x ↦ ψ₀(b x)` for some `b ∈ F^×`. Here `ψ₀` (`standardCharacter F`) is the complex-valued
  version of the Library's explicit character
  `Langlands.Automorphic.CuspidalWhittaker.adelicCharacter F`.
- `exists_eq_algebraMap_of_forall_eq_one`: if `ψ(a y) = 1` for every `a ∈ F`, then `y ∈ F`.
  That is, `F` is its own annihilator for every standard `ψ`.

## Provenance

Internal. The first result is the classical description of the characters of `𝔸/F` (Tate's
thesis, Theorem 4.1.4). It is proved here by Fourier analysis on the compact group `𝔸/F`. It
uses the Library's self-duality of `F` for `ψ₀` (`exists_eq_algebraMap_of_orthogonal`) and the
module `EqualAnalyticFourierSeries`; no local duality is needed. The Library also contains
`AdelicAdditiveDualityStatement` with a proof, which gives the annihilator statement by a
different route.

## Declarations

- `integral_eq_zero_of_mul_apply`: a multiplicative function `χ` with `χ y ≠ 1` for some `y` has
  integral zero for any left-invariant measure. Indeed `∫ χ = χ(y) ∫ χ`.
- `quotientLift`, `mk_quotientLift`, `exists_quotientLift_mk`, `exists_quotientLift_add`: a chosen lift
  `𝔸/F → 𝔸` and its compatibility with the quotient map.
- `descend F f hf hper : C(𝔸/F, ℂ)`: the descent of a continuous `F`-periodic function, with
  `descend_mk`.
- `scaledCharacter F ψ hψ htriv a`: the character `x ↦ ψ(a x)` of `𝔸/F`, for `ψ` trivial on `F`,
  with `scaledCharacter_mk`, `scaledCharacter_apply`, `scaledCharacter_add_apply`.
- `standardCharacter F`: `ψ₀` with complex values, with `standardCharacter_apply`,
  `continuous_standardCharacter`, `standardCharacter_algebraMap`, `standardCharacter_eq_one_iff`.
- `isCharacterFamily_standard`: `a ↦ (x ↦ ψ₀(a x))` is a character family in the sense of
  `IsCharacterFamily`.
- `standard_separates`: these characters separate the points of `𝔸/F`. This is the Library's
  `exists_eq_algebraMap_of_orthogonal`.
- `integral_standard_eq_zero`: for `a ≠ 0`, `∫_{𝔸/F} ψ₀(a x) dx = 0` (Library
  `exists_adelicCharacter_ne_one`).
- `exists_eq_standardCharacter_mul`. Let `χ` be `ψ` descended to `𝔸/F`. If `χ` were different
  from every `ψ₀(a ·)`, then `χ · conj ψ₀(a ·)` would be a nontrivial character for every `a`.
  All Fourier coefficients of `χ` would then vanish, so `χ = 0` by
  `eq_zero_of_fourierCoeff_eq_zero`, which is impossible since `χ(0) = 1`. So `ψ = ψ₀(b ·)`, and
  `b ≠ 0` because `ψ ≠ 1`.
- `exists_eq_algebraMap_of_forall_eq_one`: apply the classification and the Library's
  self-duality to `ψ₀(b ·)`.
