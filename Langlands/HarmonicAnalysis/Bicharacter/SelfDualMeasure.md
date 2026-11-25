# Dual and self-dual Haar measures of a self-dual bicharacter

**GKT Appendix 1.A**, self-dual case: Theorem 1.37 (p. 43) and Remark 1.38 (p. 44) for `H = G`
with a symmetric pairing, **Proposition 1.39** (p. 44) and **Definition 1.40** (p. 45).

The module `Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure` attaches to a Haar measure `μ`
on `X` and a self-dual bicharacter `e` (`IsSelfDualBicharacter`) the constant of Fourier inversion,
the dual Haar measure, and the self-dual Haar measure. `X` is a commutative, locally compact,
second countable topological group with arbitrarily large and small compact open subgroups
(`CompactOpenExhaustion`); for instance a finite-dimensional vector space over a nonarchimedean
local field with `e = ψ ∘ β`, `β` symmetric and non-degenerate (`isSelfDualBicharacter_of_symm`).
The Fourier transform is `bicharacterFourier μ e φ x = ∫ e(x, y) φ(y) dμ(y)`.

## Content

- `bicharacterFourierConstant μ e : ℝ`: the constant `C(μ) > 0` with
  `ℱ_μ ℱ_μ φ (x) = C(μ) φ(-x)` for every Schwartz–Bruhat function `φ`
  (`bicharacterFourier_bicharacterFourier_eq`, from `exists_pos_bicharacterFourier_bicharacterFourier`
  of `Bicharacter/Fourier.lean`); it is the `C` of any such formula (`bicharacterFourierConstant_eq`),
  positive (`bicharacterFourierConstant_pos`), and `C(rμ) = r² C(μ)` because `ℱ_{rμ} = r ℱ_μ`
  (`bicharacterFourierConstant_smul`, `bicharacterFourier_smul_measure`). It is defined by choice,
  with the value `1` when no such constant exists. In GKT's notation (3.4), for `e = ψ ∘ b`,
  `C(dx) = |β_b|⁻¹`.
- `bicharacterDualMeasure μ e = C(μ)⁻¹ μ`: the **dual Haar measure** of Theorem 1.37 (b) for
  `H = G`, `α = e`.
  - `bicharacterFourier_bicharacterDualMeasure`: `ℱ_{μ'} ℱ_μ φ = φ(-·)` (Theorem 1.37 (d)).
  - `eq_bicharacterDualMeasure`: a Haar measure `ν` with `ℱ_ν ℱ_μ φ = φ(-·)` for all `φ` is `μ'`
    (uniqueness in Theorem 1.37 (b)); proof: `ν = s μ` and the formula at `0` for the indicator of a
    compact open subgroup gives `s C(μ) = 1`.
  - `lintegral_enorm_bicharacterFourier_sq_bicharacterDualMeasure`:
    `∫⁻ ‖ℱ_μ φ‖ₑ² dμ' = ∫⁻ ‖φ‖ₑ² dμ`, `ℱ_μ` is an isometry `L²(μ) → L²(μ')` (Theorem 1.37 (b), from
    Plancherel's formula `lintegral_enorm_bicharacterFourier_sq`).
  - Remark 1.38: `(rμ)' = r⁻¹ μ'` (`bicharacterDualMeasure_smul`) and `μ'' = μ`
    (`bicharacterDualMeasure_bicharacterDualMeasure`).
- `selfDualMeasure e`: **the self-dual Haar measure** (Definition 1.40), defined as a Haar measure
  `μ` with `ℱ_μ ℱ_μ φ = φ(-·)` for all `φ` (by choice; `0` if there is none). Proposition 1.39:
  - `selfDualMeasure_eq_smul`: `selfDualMeasure e = C(μ)^{-1/2} μ` for every Haar measure `μ`
    (`C(C(μ)^{-1/2} μ) = 1`, and two Haar measures with constant `1` are equal since `C(sμ) = s² C(μ)`);
  - `isAddHaarMeasure_selfDualMeasure`, `bicharacterFourierConstant_selfDualMeasure` (`= 1`),
    `bicharacterFourier_bicharacterFourier_selfDualMeasure` (`ℱ ℱ φ = φ(-·)`),
    `bicharacterDualMeasure_selfDualMeasure` (it is dual to itself);
  - `eq_selfDualMeasure_iff`: a Haar measure satisfies `ℱ_μ ℱ_μ φ = φ(-·)` for all `φ` if and only
    if it is `selfDualMeasure e` (existence and uniqueness);
  - `lintegral_enorm_bicharacterFourier_sq_selfDualMeasure`: `ℱ` is an isometry of `L²` for it.

The book proves Proposition 1.39 from Theorem 1.37, which it cites as well known; here the constant
of Fourier inversion is computed in `Bicharacter/Fourier.lean` on indicators of compact open
subgroups, so nothing is cited. The case of two different groups (Theorem 1.37 in general) is
`Langlands/HarmonicAnalysis/Bicharacter/DualMeasure.lean`, which also identifies the dual measure
of this page with the dual measure of the perfect pairing `e` of `X` with itself.

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), Appendix
1.A: Theorem 1.37, p. 43; Remark 1.38 and Proposition 1.39, p. 44; Definition 1.40, p. 45.

## Declarations

- `Langlands.HarmonicAnalysis.bicharacterFourierConstant`, `bicharacterDualMeasure`,
  `selfDualMeasure`, `bicharacterFourierConstant_pos`, `bicharacterFourier_smul_measure`,
  `bicharacterFourier_const_mul`.
- `exists_mem_schwartzBruhatSubmodule_apply_zero`, `bicharacterFourierConstant_eq`,
  `bicharacterFourier_bicharacterFourier_eq`, `bicharacterFourierConstant_smul`.
- `bicharacterFourier_bicharacterDualMeasure`, `eq_bicharacterDualMeasure`,
  `bicharacterDualMeasure_smul`, `bicharacterDualMeasure_bicharacterDualMeasure`,
  `lintegral_enorm_bicharacterFourier_sq_bicharacterDualMeasure`.
- `selfDualMeasure_eq_smul`, `isAddHaarMeasure_selfDualMeasure`,
  `bicharacterFourierConstant_selfDualMeasure`, `bicharacterFourier_bicharacterFourier_selfDualMeasure`,
  `eq_selfDualMeasure_iff`, `bicharacterDualMeasure_selfDualMeasure`,
  `lintegral_enorm_bicharacterFourier_sq_selfDualMeasure`.

## Dependencies

`Langlands.HarmonicAnalysis.Bicharacter.Fourier` (and through it `Bicharacter.SelfDual`).
