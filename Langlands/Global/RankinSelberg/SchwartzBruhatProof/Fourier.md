# Fourier inversion on `S(𝔸^n)`

Module `Langlands.Global.RankinSelberg.SchwartzBruhatProof.Fourier`, namespace
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof`. It proves the Fourier clauses of
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement`:

```
theorem fourierTransform_mem_and_inversion (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) :
    fourierTransform F n ψ Φ ∈ schwartzBruhat F n ∧
      ∀ x, fourierTransform F n ψ (fourierTransform F n ψ Φ) x = Φ (-x)
```

`F` is a number field with `CompactSpace (AdeleQuotient F)`. The transform is the Library's
`fourierTransform F n ψ` for `rectangleMeasure F 1 n`.

## Provenance and route

This is Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Lemma C.3.1 and the
inversion formula (C.6), printed p.554 (registered as
`getz-hahn-2024-automorphic-representations`), for the measure with `F^n \ 𝔸^n` of volume one.
Tate's thesis (Theorems 4.1.1–4.1.3) explains why this measure is self-dual.

The Lean proof does not compute the self-dual measure place by place. It shows that inversion
holds up to a constant on pure tensors, and then uses Poisson summation to show that the
constant is `1`:

1. Write `ψ = ψ₀(b ·)` with `b ∈ F^×` (`EqualAnalytic.exists_eq_standardCharacter_mul`). The
   Library's `EqualAnalytic.fourierTransform_pure` splits the transform of a pure tensor
   `Φ_∞ ⊗ Φ_f` as `c_n F_∞ Φ_∞ ⊗ F_f Φ_f`. Here `c_n = EqualAnalytic.rowConstant F n` compares
   `rectangleMeasure` with the product of the archimedean and finite Haar measures. `F_∞` is
   `pairingFourier` (module `ArchFourier`) for the pairing
   `traceBilin F n (b) (w, ξ) = Tr_∞(b Σ_j w_j ξ_j)`, and `F_f` is `finFourier` (module
   `FiniteFourier`) for `rowPairing ψ n` and `Measure.addHaar` on `𝔸_f^n`.
2. `exists_pairingFourier_inversion` gives `C` with `F_∞ F_∞ φ = C φ(-·)` on Schwartz
   functions. `finiteFourier_inversion` gives
   `F_f F_f Φ_f = ν(L_m^n) ν(L_(n_ψ - m)^n) Φ_f(-·)` for `L_m^n`-invariant `Φ_f`. So the double
   transform of such a pure tensor is `K_m Φ(-x)` with
   `K_m = c_n² C ν(L_m^n) ν(L_(n_ψ - m)^n)` (`inversionConstant`).
3. `K_m = 1`. Take `Φ⁰ = G ⊗ 1_(L_m^n)` with `G ≥ 0` a smooth compactly supported bump function
   with `G(0) = 1`. Poisson summation (`EqualAnalytic.hasSum_poisson`) applied to `Φ⁰` and to
   `Φ̂⁰` gives `Σ_(ξ ∈ F^n) Φ̂̂⁰(ξ) = Σ_ξ Φ̂⁰(ξ) = Σ_ξ Φ⁰(ξ) = S`. Here `Φ̂⁰` lies in
   `schwartzBruhat F n` by step 2. Also by step 2 the left side is
   `K_m Σ_ξ Φ⁰(-ξ) = K_m S`, reindexing by `ξ ↦ -ξ`. Every term `Φ⁰(ξ)` has nonnegative real part and `Φ⁰(0) = 1`, so
   `Re S ≥ 1`, hence `S ≠ 0` and `K_m = 1`.
4. Every element of `schwartzBruhat F n` is a finite linear combination of pure tensors. Each
   pure tensor has an `L_m^n`-invariant finite part for some `m`
   (`exists_latticeVec_invariant`). Linearity of the transform
   (`EqualAnalytic.fourierTransform_add`, `fourierTransform_smul`, `fourierTransform_zero`)
   completes the proof by span induction.

## Declarations

- `archimedeanCoordinates_zero`, `archimedeanCoordinates_neg`, `finiteCoordinates_zero`,
  `finiteCoordinates_neg`: the coordinate maps `𝔸^n → F_∞^n`, `𝔸^n → 𝔸_f^n` preserve `0` and
  negation. They follow from the Library additivity lemmas.
- `traceBilin_symm`: `traceBilin F n (b)` is symmetric. `traceBilin_nondegenerate` (for `b ≠ 0`):
  its right kernel is trivial, by `EqualAnalytic.tracePairing_separates` with the inverse `b⁻¹`.
- `pairingFourier_const_mul`: `F_∞(c φ) = c F_∞ φ`.
- `fourierTransform_pure_eq`: step 1, a restatement of `fourierTransform_pure` in terms of
  `pairingFourier` and `finFourier`.
- `inversionConstant n ψ hψ C m = c_n² C ν(L_m^n) ν(L_(n_ψ - m)^n)`.
- `pure_inversion`: assume `C` is an inversion constant for `F_∞` on Schwartz functions, and let
  `Φ_f` be compactly supported and `L_m^n`-invariant. Then the transform of `Φ_∞ ⊗ Φ_f` is the
  pure tensor `(c_n F_∞ Φ_∞) ⊗ F_f Φ_f`, so it lies in the spanning set of `schwartzBruhat`.
  Its double transform is `inversionConstant · Φ(-x)`.
- `inversionConstant_eq_one`: step 3. `G` comes from Mathlib's
  `exists_contDiff_tsupport_subset` (smooth, compact support, values in `[0, 1]`, `G(0) = 1`).
  It becomes a Schwartz function by `HasCompactSupport.toSchwartzMap`. The sum `S` is summable by
  `EqualAnalytic.summable_periodization`. The real-part estimate uses `Complex.hasSum_re` and
  `le_hasSum`.
- `fourierTransform_mem_and_inversion`: step 4, the main result.
