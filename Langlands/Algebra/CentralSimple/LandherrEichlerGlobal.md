# Reduction of Landherr's theorem to relative reduced norm one

Module: `Langlands.Algebra.CentralSimple.LandherrEichlerGlobal`.

Let `F` be a number field, `E/F` a separable quadratic extension, `B` a finite-dimensional
central simple `E`-algebra which is an `F`-algebra through `E`, and
`τ : FirstKindInvolution F B` acting on `E` by the conjugation `σ`. Let
`relNorm F E B F : F ⊗_F B → E ⊗_F F` be the relative reduced norm (module
`Langlands.Algebra.CentralSimple.LandherrNonsplitLocal`).

- `relNorm_one_tmul`: `relNorm F E B F (1 ⊗ z) = Nrd_{B/E}(z) ⊗ 1`.
- `exists_relNorm_eq_one`: if `y ∈ Bˣ` is `τ`-symmetric and at every place `v` of `F` there is
  a unit `x_v` of `F_v ⊗_F B` with `1 ⊗ y = x_v τ_v(x_v)`, then there is `b ∈ Bˣ` such that
  `b⁻¹ y τ(b⁻¹)` has relative reduced norm one.

## Proof of `exists_relNorm_eq_one`

1. By `exists_relNorm_eq_qm`, `relNorm (1 ⊗ y) = a₀ ∈ F`, and `a₀ ≠ 0` because `y` is a unit.
   By `relNorm_mul_conj_of_eq`, `δ_v = relNorm(x_v)` satisfies `δ_v σ(δ_v) = a₀` at every place
   `v`, so `a₀` is a local norm from `E ⊗_F F_v` everywhere. The Hasse norm theorem for the
   cyclic extension `E/F` (`QuadraticNormLocalGlobal.exists_eq_of_local` with
   `ClassFieldTheory.Global.cyclicHasseNorm`) gives `t₀ ∈ E` with `t₀ σ(t₀) = a₀`.
2. At each place `v`, local Hilbert 90 (`exists_hilbert90_point`) gives a unit
   `ω_v = qm P_v Q_v` with `δ_v σ(ω_v) = (t₀ ⊗ 1) ω_v`.
3. For each place `w` of `E` over `v` which is infinite, or finite and among the finitely many
   places where `E_w ⊗_E B` is not split (`Brauer.finite_nonsplitFinitePlaces`),
   `exists_reducedNorm_near_hilbert90` (module
   `Langlands.Algebra.CentralSimple.LandherrEichlerLocal`) gives a neighbourhood of
   `(P_v, Q_v)` on which `t₀ ω / σ(ω)` is a local reduced norm at `w`. Finite completions of
   `E` are given the normed field structure `Valued.toNontriviallyNormedField`, and the
   archimedean ones their absolute value.
4. Weak approximation for `F` (`exists_algebraMap_mem_open`, module
   `Langlands.Global.AdelicFunctoriality.MixedWeakApproximation`), applied coordinatewise,
   gives `p, q ∈ F` in all these neighbourhoods. Put `ω = p + q r` and `t = t₀ ω / σ(ω)`;
   then `t ≠ 0`, `t σ(t) = a₀`, and `t` is a local reduced norm at every place of `E`: at the
   places of step 3 by construction and at finite places where `E_w ⊗_E B` is split by
   `reducedNormUnits_surjective_of_split`.
5. The Hasse–Schilling norm theorem `numberFieldReducedNormLocality` (module
   `Langlands.Algebra.NumberFieldReducedNormLocalityProof`) gives `b ∈ Bˣ` with
   `Nrd(b) = t`. Then
   `relNorm (b⁻¹ y τ(b⁻¹)) = t⁻¹ · a₀ · σ(t)⁻¹ = 1`, using `relNorm_baseChange` for
   `τ(b⁻¹)`.

## Provenance

This is the first step of the proof of Landherr's theorem in Kneser, *Lectures on Galois
Cohomology of Classical Groups* (1969), §5.5, printed p. 77 (PDF p. 83); compare Platonov and
Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7, Theorem 6.27, printed p. 359
(PDF p. 369). The Hasse norm theorem gives `t₀ ∈ E` with `N(t₀) = Nrd(y)`. As in Kneser's
argument, weak approximation gives a factor `ω / σ(ω)` of norm one so that
`t = t₀ ω / σ(ω)` is a local reduced norm at the archimedean places. The implementation
also makes `t` a local reduced norm at the finite places where the algebra is nonsplit.
Eichler's norm theorem then produces `b` with `Nrd(b) = t`, so that `b⁻¹ y τ(b⁻¹)` has
reduced norm one.
