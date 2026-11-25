/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Reduced fractions of complex polynomials

Two facts about a quotient `A / B` of complex polynomials with constant term `1`, used to read
off the local factors of an `L`-function from the `L`-function itself:

- if the reciprocal roots of `A` and those of `B` lie on disjoint sets of radii, then `A` and
  `B` are coprime, so `A / B` is already reduced and its poles are the reciprocal roots of `B`;
- if `A` and `B` are coprime and `A / B` has real coefficients, so have `A` and `B`.

## Main statements

- `Polynomial.isCoprime_of_norm_inv_roots`: blueprint `theorem-pure-lisse-sheaves-over-relative--1`.
- `Polynomial.map_conj_eq_self_of_isCoprime`: blueprint `theorem-pure-lisse-sheaves-over-relative`.
-/

@[expose] public section

open scoped ComplexConjugate

namespace Polynomial

/-- **Separation by root radii.** Let `A` and `B` be nonzero complex polynomials. If every root
`z` of `A` has `‖z‖⁻¹ ≤ R` and every root `z` of `B` has `‖z‖⁻¹ = S` with `R < S`, then `A` and
`B` are coprime. For `A` and `B` with constant term `1` the numbers `z⁻¹` are their reciprocal
roots, so this says that no reciprocal root of `B` cancels in the fraction `A / B`: its
reciprocal poles of modulus `S` are exactly the reciprocal roots of `B`, with multiplicity
(blueprint: `theorem-pure-lisse-sheaves-over-relative--1`). -/
theorem isCoprime_of_norm_inv_roots {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) {R S : ℝ}
    (hAR : ∀ z ∈ A.roots, ‖z‖⁻¹ ≤ R) (hBS : ∀ z ∈ B.roots, ‖z‖⁻¹ = S) (hRS : R < S) :
    IsCoprime A B := by
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ A B).2 fun z ↦ ?_
  by_contra! h
  have hAz := hAR z ((mem_roots hA).2 (by simpa using h.1))
  have hBz := hBS z ((mem_roots hB).2 (by simpa using h.2))
  linarith

/-- A divisor `A` of its own complex conjugate `Ā` with constant term `1` is real. -/
private theorem map_conj_eq_self_of_dvd {A : ℂ[X]} (hA : A.coeff 0 = 1)
    (hdvd : A ∣ A.map (starRingEnd ℂ)) : A.map (starRingEnd ℂ) = A := by
  obtain ⟨D, hD⟩ := hdvd
  have hA0 : A ≠ 0 := fun h ↦ by simp [h] at hA
  have hconj0 : A.map (starRingEnd ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (starRingEnd ℂ).injective).2 hA0
  have hD0 : D ≠ 0 := by rintro rfl; exact hconj0 (by rw [hD, mul_zero])
  have hdeg : D.natDegree = 0 := by
    have := congrArg natDegree hD
    rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective, natDegree_mul hA0 hD0] at this
    omega
  have hcoeff : D.coeff 0 = 1 := by
    have := congrArg (coeff · 0) hD
    simp only [coeff_map, hA, map_one, mul_coeff_zero, one_mul] at this
    exact this.symm
  rw [hD, eq_C_of_natDegree_eq_zero hdeg, hcoeff, C_1, mul_one]

/-- **Reality of coprime factors.** Let `A` and `B` be coprime complex polynomials with constant
term `1` such that the fraction `A / B` is fixed by complex conjugation, `A B̄ = Ā B`, that is,
`A / B ∈ ℝ(T)`. Then `A` and `B` have real coefficients
(blueprint: `theorem-pure-lisse-sheaves-over-relative`). -/
theorem map_conj_eq_self_of_isCoprime {A B : ℂ[X]} (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hAB : IsCoprime A B) (h : A * B.map (starRingEnd ℂ) = A.map (starRingEnd ℂ) * B) :
    A.map (starRingEnd ℂ) = A ∧ B.map (starRingEnd ℂ) = B :=
  ⟨map_conj_eq_self_of_dvd hA (hAB.dvd_of_dvd_mul_right ⟨_, h.symm⟩),
    map_conj_eq_self_of_dvd hB (hAB.symm.dvd_of_dvd_mul_left ⟨_, h.trans (mul_comm _ _)⟩)⟩

end Polynomial
