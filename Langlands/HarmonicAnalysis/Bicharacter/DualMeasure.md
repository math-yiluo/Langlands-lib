# Dual Haar measures of a perfect pairing

**GKT Appendix 1.A**: **Theorem 1.37** (p. 43), **Remark 1.38** (p. 44), and the special case
(1.12) of a non-degenerate bilinear pairing of vector spaces (p. 45).

The module `Langlands.HarmonicAnalysis.Bicharacter.DualMeasure` proves the Fourier inversion and
Plancherel formulas for a perfect pairing `α : X × Y → ℂ¹` of two totally disconnected groups and
constructs the dual Haar measure. `X` and `Y` are commutative, locally compact, second countable
topological groups with arbitrarily large and small compact open subgroups
(`CompactOpenExhaustion`), `μ` and `ν` Haar measures on them.

## Content

- `IsPerfectBicharacter α`: `α : X → Y → ℂ` is a bicharacter of modulus one, locally constant on
  `X × Y`, and the annihilators identify each group with the dual of the other: the annihilator
  in `Y` (resp. `X`) of a large compact subset of `X` (resp. `Y`) lies in a given neighbourhood of
  `0` (`small_left`, `small_right`), and the annihilator of a neighbourhood of `0` lies in a compact
  set (`big_left`, `big_right`). This is the book's "perfect pairing" in the form the Fourier
  analysis of totally disconnected groups uses. `IsPerfectBicharacter.flip`: the flipped pairing
  `(y, x) ↦ α(x, y)` is perfect; `annihilator`, `isOpen_annihilator`, `isCompact_annihilator`.
- `pairingFourier μ α φ y = ∫ α(x, y) φ(x) dμ(x)` and `pairingFourierDual ν α f x = ∫ α(x, y) f(y) dν(y)`
  (the book's `F_{dg}`, `F_{dh}`).
- Theorem 1.37 (a): `pairingFourier_mem`, `pairingFourierDual_mem`: both transforms preserve
  Schwartz–Bruhat functions (local constancy from the compactness of the support; compact support
  because `ℱ_μ φ (y) = α(t, y) ℱ_μ φ (y)` for every small `t` under which `φ` is invariant).
- Theorem 1.37 (d) up to the normalization of the measures:
  `exists_pos_pairingFourierDual_pairingFourier`, and with the constant
  `pairingFourierConstant μ ν α > 0` (defined by choice, `1` if there is none):
  `pairingFourierDual_pairingFourier_eq`: `ℱ'_ν ℱ_μ φ = C φ(-·)`, and
  `pairingFourier_pairingFourierDual_eq`: `ℱ_μ ℱ'_ν f = C f(-·)` with the **same** constant
  (`pairingFourierConstant_flip`). Proof of the first: for `φ` invariant under `A = M^⊥`, `M ⊆ Y` a
  compact open subgroup, `ℱ_μ φ` vanishes off `B = A^⊥`, the transform of the indicator of `B` is
  `ν(B)` times the indicator of `B^⊥ = A`, and Fubini on `B × supp φ` gives `C = μ(A) ν(B)`; the
  constant does not depend on `M` (compare at the indicator of one compact open subgroup). For the
  second: apply `ℱ_μ` to the first formula for the indicator of a compact open subgroup `L` at `0`
  (`pairingFourier_comp_neg`).
- Theorem 1.37 (b), (c) up to the normalization: `lintegral_enorm_pairingFourier_sq`
  (`∫⁻ ‖ℱ_μ φ‖ₑ² dν = C ∫⁻ ‖φ‖ₑ² dμ`), `lintegral_enorm_pairingFourierDual_sq`.
  `C(rμ, ν) = r C(μ, ν)`, `C(μ, rν) = r C(μ, ν)` (`pairingFourierConstant_smul_left`, `…_right`).
- **The dual measure** `pairingDualMeasure μ α`, defined as a Haar measure `ν` on `Y` with
  `ℱ'_ν ℱ_μ φ = φ(-·)` for all `φ` (by choice):
  - `pairingDualMeasure_eq_smul`: it is `C(μ, ν)⁻¹ ν` for every Haar measure `ν` (existence and
    uniqueness), `isAddHaarMeasure_pairingDualMeasure`, `pairingFourierConstant_pairingDualMeasure`;
  - Theorem 1.37 (d): `pairingFourierDual_pairingDualMeasure_pairingFourier`,
    `pairingFourier_pairingFourierDual_pairingDualMeasure`;
  - Theorem 1.37 (b), (c): `lintegral_enorm_pairingFourier_sq_pairingDualMeasure`,
    `lintegral_enorm_pairingFourierDual_sq_pairingDualMeasure` (both transforms are isometries);
  - `eq_pairingDualMeasure_iff`: uniqueness;
  - Remark 1.38: `pairingDualMeasure_smul` (`(rμ)' = r⁻¹ μ'`) and
    `pairingDualMeasure_pairingDualMeasure` (the dual of `μ'` for the flipped pairing is `μ`).
- The self-dual case: `IsSelfDualBicharacter.isPerfectBicharacter`;
  `pairingFourier_eq_bicharacterFourier` for a symmetric bicharacter;
  `pairingDualMeasure_eq_bicharacterDualMeasure`: the dual measure of this page is the
  `bicharacterDualMeasure` of `Bicharacter/SelfDualMeasure.lean`.
- (1.12): `isPerfectBicharacter_of_nondegenerate`: for a nonarchimedean local field `F`, a
  non-trivial continuous unitary character `ψ` and a non-degenerate bilinear pairing
  `⟨,⟩ : X × Y → F` of finite-dimensional spaces with their module topologies, `ψ ∘ ⟨,⟩` is perfect.
  Proof: the symmetric form `((x, y), (x', y')) ↦ ⟨x, y'⟩ + ⟨x', y⟩` on `X × Y` is non-degenerate,
  so `isSelfDualBicharacter_of_symm` applies, and the four conditions are read off on `X × 0` and
  `0 × Y`.

The book cites Theorem 1.37 as well known ("They are all well-known and can be found in most
textbooks on this subject", p. 43); here it is proved for totally disconnected groups.
The book's formula (1.12) (p. 45) has misprints: its left sides read `F_{dx}(φ)(x)` and
`F_{dy}(f)(y)` for `F_{dx}(φ)(y)` and `F_{dy}(f)(x)`, and the second isometry is written `F_{dh}` for
`F_{dy}`.

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), Appendix
1.A: Theorem 1.37, p. 43; Remark 1.38, p. 44; (1.12), p. 45.

## Declarations

- `Langlands.HarmonicAnalysis.IsPerfectBicharacter` with `flip`, `ne_zero`, `map_zero_left`,
  `map_neg_left`, `conj_apply`, `map_neg_left_eq_map_neg_right`, `continuous`, `annihilator`,
  `mem_annihilator`, `isOpen_annihilator`, `isCompact_annihilator`.
- `pairingFourier`, `pairingFourierDual`, `pairingFourier_apply`, `pairingFourierDual_apply`,
  `pairingFourier_const_mul`, `pairingFourier_smul_measure`.
- `pairingFourier_mem`, `pairingFourierDual_mem`, `exists_pos_pairingFourierDual_pairingFourier`.
- `pairingFourierConstant`, `pairingDualMeasure`, `pairingFourierConstant_pos`,
  `pairingFourierConstant_eq`, `pairingFourierDual_pairingFourier_eq`, `pairingFourier_comp_neg`,
  `pairingFourier_pairingFourierDual_eq`, `lintegral_enorm_pairingFourier_sq`,
  `pairingFourierConstant_flip`, `lintegral_enorm_pairingFourierDual_sq`,
  `pairingFourierConstant_smul_right`, `pairingFourierConstant_smul_left`.
- `pairingDualMeasure_eq_smul`, `isAddHaarMeasure_pairingDualMeasure`,
  `pairingFourierConstant_pairingDualMeasure`, `pairingFourierDual_pairingDualMeasure_pairingFourier`,
  `pairingFourier_pairingFourierDual_pairingDualMeasure`,
  `lintegral_enorm_pairingFourier_sq_pairingDualMeasure`,
  `lintegral_enorm_pairingFourierDual_sq_pairingDualMeasure`, `eq_pairingDualMeasure_iff`,
  `pairingDualMeasure_smul`, `pairingDualMeasure_pairingDualMeasure`.
- `IsSelfDualBicharacter.isPerfectBicharacter`, `pairingFourier_eq_bicharacterFourier`,
  `pairingDualMeasure_eq_bicharacterDualMeasure`, `isPerfectBicharacter_of_nondegenerate`.

Internal (`Langlands.HarmonicAnalysis.PairingFourier.Internal`): `pairingFourier_eq_zero`,
`pairingFourier_indicator`, `exists_of_annihilator_invariant`, `exists_of_invariant`.

## Dependencies

`Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure` (and through it `Bicharacter.Fourier`,
`Bicharacter.SelfDual`).
