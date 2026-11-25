/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Functions on `ℕ` with polynomial forward differences

We show that a function `f : ℕ → ℚ` whose forward difference agrees with a polynomial of degree
`< d` on the naturals is itself given by a polynomial of degree `< d + 1`, and that the same holds
if only the differences with two coprime steps `a` and `a + 1` are polynomial. We also record a few
facts on polynomials which are eventually nonnegative on the naturals, and on the degree of the
difference `P (X + a) - P`.

## Main statements

- `Polynomial.exists_degree_lt_eval_eq_of_fwdDiff_iter_eq_zero`: a function on `ℕ` whose
  `(d + 1)`-st forward difference vanishes is a polynomial of degree `< d + 1` (Newton series).
- `Polynomial.exists_degree_lt_eval_eq_of_sub`: a function on `ℕ` whose forward difference is a
  polynomial of degree `< d` is a polynomial of degree `< d + 1`.
- `Polynomial.exists_degree_lt_eval_eq_of_sub_of_sub`: the same with steps `a` and `a + 1`.
- `Polynomial.leadingCoeff_nonneg_of_eventually_nonneg`,
  `Polynomial.degree_le_degree_add_of_eventually_nonneg`: eventually nonnegative polynomials.
- `Polynomial.degree_add_one_le_of_le_degree_comp_sub`: the difference `P (X + a) - P` has
  degree smaller than `P`.
-/

@[expose] public section

open Finset Filter fwdDiff Nat

/-- Iterated forward differences with step `1` commute with restriction along `ℕ → R`. -/
theorem fwdDiff_iter_comp_natCast {R G : Type*} [AddCommMonoidWithOne R] [AddCommGroup G]
    (g : R → G) (k n : ℕ) : Δ_[1]^[k] (fun m : ℕ ↦ g m) n = Δ_[1]^[k] g n := by
  simp [fwdDiff_iter_eq_sum_shift]

/-- The iterated forward difference of the zero function vanishes. -/
theorem fwdDiff_iter_zero {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M) (k : ℕ) :
    Δ_[h]^[k] (0 : M → G) = 0 :=
  Function.iterate_fixed (fwdDiff_const h (0 : G)) k

namespace Polynomial

/-- **Newton series.** A function `f : ℕ → ℚ` whose `(d + 1)`-st forward difference vanishes
agrees on the naturals with a polynomial of degree `< d + 1`. -/
theorem exists_degree_lt_eval_eq_of_fwdDiff_iter_eq_zero {f : ℕ → ℚ} {d : ℕ}
    (hf : Δ_[1]^[d + 1] f = 0) :
    ∃ P : ℚ[X], P.degree < d + 1 ∧ ∀ n : ℕ, P.eval (n : ℚ) = f n := by
  refine ⟨∑ k ∈ range (d + 1), (Δ_[1]^[k] f 0 / k !) • descPochhammer ℚ k, ?_, fun n ↦ ?_⟩
  · refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2
      fun k hk ↦ (degree_smul_le _ _).trans_lt ?_)
    rw [degree_eq_natDegree (monic_descPochhammer ℚ k).ne_zero, descPochhammer_natDegree]
    exact_mod_cast mem_range.1 hk
  · have hN := shift_eq_sum_fwdDiff_iter 1 f n 0
    simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at hN
    rw [hN, eval_finsetSum]
    simp_rw [eval_smul, smul_eq_mul, cast_choose_eq_descPochhammer_div]
    rw [sum_subset (range_subset_range.2 (by omega : d + 1 ≤ n + d + 1)),
      sum_subset (range_subset_range.2 (by omega : n + 1 ≤ n + d + 1))]
    · exact sum_congr rfl fun k _ ↦ by ring
    · intro k _ hk
      rw [← cast_choose_eq_descPochhammer_div,
        choose_eq_zero_of_lt (by simpa using hk), cast_zero, zero_mul]
    · intro k _ hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 (mem_range.not.1 hk))
      rw [add_comm, Function.iterate_add_apply, hf, fwdDiff_iter_zero]
      simp

/-- A function `f : ℕ → ℚ` whose forward difference agrees on the naturals with a polynomial of
degree `< d` agrees on the naturals with a polynomial of degree `< d + 1`. -/
theorem exists_degree_lt_eval_eq_of_sub {f : ℕ → ℚ} {d : ℕ} {Q : ℚ[X]} (hQ : Q.degree < d)
    (hf : ∀ n : ℕ, f (n + 1) - f n = Q.eval (n : ℚ)) :
    ∃ P : ℚ[X], P.degree < d + 1 ∧ ∀ n : ℕ, P.eval (n : ℚ) = f n := by
  refine exists_degree_lt_eval_eq_of_fwdDiff_iter_eq_zero ?_
  funext n
  have hΔ : Δ_[1] f = fun m : ℕ ↦ Q.eval (m : ℚ) := by
    ext m
    exact hf m
  rw [Function.iterate_succ_apply, hΔ]
  refine (fwdDiff_iter_comp_natCast (fun x : ℚ ↦ Q.eval x) d n).trans ?_
  by_cases hQ0 : Q = 0
  · subst hQ0
    simp only [eval_zero]
    exact congrFun (fwdDiff_iter_zero (1 : ℚ) d) _
  · rw [fwdDiff_iter_eq_zero_of_degree_lt ((natDegree_lt_iff_degree_lt hQ0).2 hQ)]
    rfl

/-- **Coprime steps.** A function `f : ℕ → ℚ` whose differences with steps `a` and `a + 1` both
agree on the naturals with polynomials of degree `< d` agrees on the naturals with a polynomial of
degree `< d + 1`: indeed `f (n + 1) - f n = B n - A (n + 1)`. -/
theorem exists_degree_lt_eval_eq_of_sub_of_sub {f : ℕ → ℚ} {d a : ℕ} {A B : ℚ[X]}
    (hA : A.degree < d) (hB : B.degree < d) (hfA : ∀ n : ℕ, f (n + a) - f n = A.eval (n : ℚ))
    (hfB : ∀ n : ℕ, f (n + (a + 1)) - f n = B.eval (n : ℚ)) :
    ∃ P : ℚ[X], P.degree < d + 1 ∧ ∀ n : ℕ, P.eval (n : ℚ) = f n := by
  refine exists_degree_lt_eval_eq_of_sub (Q := B - taylor 1 A) ?_ fun n ↦ ?_
  · exact (degree_sub_le _ _).trans_lt (max_lt hB (by rwa [degree_taylor]))
  · have h₁ := hfA (n + 1)
    have h₂ := hfB n
    rw [add_right_comm] at h₁
    rw [eval_sub, taylor_eval, ← h₂, ← cast_add_one, ← h₁, ← add_assoc]
    ring

/-- A polynomial which is eventually nonnegative on the naturals has nonnegative leading
coefficient. -/
theorem leadingCoeff_nonneg_of_eventually_nonneg {P : ℚ[X]}
    (hP : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  obtain ⟨N, hN⟩ := hP
  by_contra! h
  rcases le_or_gt P.degree 0 with h0 | h0
  · have hN' := hN N le_rfl
    rw [eq_C_of_degree_le_zero h0] at hN' h
    simp only [eval_C, leadingCoeff_C] at hN' h
    exact hN'.not_gt h
  · have := (P.tendsto_atBot_of_leadingCoeff_nonpos h0 h.le).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn, hnN⟩ :=
      ((this.eventually (eventually_lt_atBot 0)).and (eventually_ge_atTop N)).exists
    exact (hN n hnN).not_gt hn

/-- Adding a polynomial which is eventually nonnegative on the naturals to another such
polynomial does not lower the degree: the leading coefficients cannot cancel. -/
theorem degree_le_degree_add_of_eventually_nonneg {P Q : ℚ[X]}
    (hP : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ P.eval (n : ℚ)) (hQ : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ Q.eval (n : ℚ)) :
    P.degree ≤ (P + Q).degree := by
  rcases lt_trichotomy P.degree Q.degree with h | h | h
  · rw [degree_add_eq_right_of_degree_lt h]
    exact h.le
  · by_cases hP0 : P = 0
    · simp [hP0]
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero]
    · exact le_max_left _ _
    · have h₁ := leadingCoeff_nonneg_of_eventually_nonneg hP
      have h₂ := leadingCoeff_nonneg_of_eventually_nonneg hQ
      have h₃ : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
      exact (add_pos_of_pos_of_nonneg (lt_of_le_of_ne h₁ h₃.symm) h₂).ne'
  · rw [degree_add_eq_left_of_degree_lt h]

/-- If the difference `P (X + a) - P` has degree at least `d`, then `P` has degree at least
`d + 1`: this difference has the same leading term cancelled. -/
theorem degree_add_one_le_of_le_degree_comp_sub {P : ℚ[X]} {a d : ℕ}
    (h : (d : WithBot ℕ) ≤ (P.comp (X + C (a : ℚ)) - P).degree) :
    ((d + 1 : ℕ) : WithBot ℕ) ≤ P.degree := by
  have hP : P ≠ 0 := by
    rintro rfl
    simp at h
  rw [← taylor_apply] at h
  have hlt := degree_sub_lt_right (degree_taylor P (a : ℚ)) hP
    (leadingCoeff_taylor (a : ℚ) P)
  rw [degree_eq_natDegree hP] at hlt ⊢
  exact_mod_cast (WithBot.coe_lt_coe.1 (h.trans_lt hlt) : d < P.natDegree)

/-- For a polynomial of degree at most `g`, the `g`-th forward difference at `0` of its values at
the natural numbers is `g!` times its coefficient of `X ^ g`. -/
theorem fwdDiff_iter_eval_natCast_zero {P : ℚ[X]} {g : ℕ} (hP : P.natDegree ≤ g) :
    Δ_[1]^[g] (fun n : ℕ ↦ P.eval (n : ℚ)) 0 = g.factorial * P.coeff g := by
  rw [fwdDiff_iter_comp_natCast (fun x : ℚ ↦ P.eval x) g 0]
  rcases hP.lt_or_eq with hlt | rfl
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp
  · rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    simp [mul_comm]

/-- Shifting the variable does not change the coefficient of `X ^ g` of a polynomial of degree at
most `g`. -/
theorem coeff_comp_X_add_C_of_natDegree_le {P : ℚ[X]} {g : ℕ} (hP : P.natDegree ≤ g) (a : ℚ) :
    (P.comp (X + C a)).coeff g = P.coeff g := by
  rw [← taylor_apply]
  rcases hP.lt_or_eq with hlt | rfl
  · rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_taylor])]
  · have := leadingCoeff_taylor (r := a) (f := P)
    rwa [Polynomial.leadingCoeff, natDegree_taylor] at this

end Polynomial
