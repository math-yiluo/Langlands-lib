import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Group.Nat.Hom

/-! # Independence of exponential sequences and exponential polynomials

Two uniqueness statements for sequences `k ↦ ∑ i, ν i ^ k * Q i (k)` over a field: the plain
Vandermonde version with constant coefficients, valid over any field, and the version with
polynomial coefficients, valid in characteristic zero for nonzero distinct ratios `ν i`. -/

noncomputable section

open Polynomial

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- Vandermonde independence: if `∑ i, c i * ν i ^ k = 0` for every `k : ℕ` and the `ν i` are
distinct, then every coefficient `c i` vanishes. -/
theorem eq_zero_of_sum_mul_pow_eq_zero {ν : ι → K} (hν : Function.Injective ν) {c : ι → K}
    (h : ∀ k : ℕ, ∑ i, c i * ν i ^ k = 0) : ∀ i, c i = 0 := by
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) K).comp
    (fun i => powersHom K (ν i)) ((powersHom K).injective.comp hν)
  refine Fintype.linearIndependent_iff.1 hli c ?_
  funext k
  simpa [Finset.sum_apply] using h k.toAdd

variable [CharZero K]

open scoped Classical in
/-- The induction behind `eq_zero_of_sum_pow_mul_eval_eq_zero`, on a bound `N` for the total
size `∑ i, (natDegree (Q i) + 1)` of the nonzero coefficient polynomials. -/
theorem eq_zero_of_sum_pow_mul_eval_eq_zero_of_le {ν : ι → K} (hν : Function.Injective ν)
    (hν0 : ∀ i, ν i ≠ 0) (N : ℕ) :
    ∀ Q : ι → K[X], ∑ i, (if Q i = 0 then 0 else (Q i).natDegree + 1) ≤ N →
      (∀ k : ℕ, ∑ i, ν i ^ k * (Q i).eval (k : K) = 0) → ∀ i, Q i = 0 := by
  classical
  induction N with
  | zero =>
    intro Q hQ _ i
    have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hQ)) i (Finset.mem_univ i)
    by_contra hi
    simp [hi] at this
  | succ N ih =>
    intro Q hQ h
    by_contra hne
    obtain ⟨j, hj⟩ := not_forall.1 hne
    -- the difference operator `a ↦ (k ↦ a (k + 1) - ν j * a k)` on coefficient polynomials
    set Q' : ι → K[X] := fun i => C (ν i) * taylor 1 (Q i) - C (ν j) * Q i with hQ'
    have h' : ∀ k : ℕ, ∑ i, ν i ^ k * (Q' i).eval (k : K) = 0 := by
      intro k
      have e : ∀ i, ν i ^ k * (Q' i).eval (k : K) =
          ν i ^ (k + 1) * (Q i).eval ((k + 1 : ℕ) : K) -
            ν j * (ν i ^ k * (Q i).eval (k : K)) := by
        intro i
        simp only [hQ', eval_sub, eval_mul, eval_C, taylor_eval, Nat.cast_succ]
        ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, h, mul_zero, sub_zero]
    have hle : ∀ i, (if Q' i = 0 then 0 else (Q' i).natDegree + 1) ≤
        (if Q i = 0 then 0 else (Q i).natDegree + 1) := by
      intro i
      by_cases hi : Q i = 0
      · have : Q' i = 0 := by simp [hQ', hi]
        simp [this, hi]
      · have hdeg : (Q' i).natDegree ≤ (Q i).natDegree := by
          refine (natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans
            (natDegree_taylor _ _).le) (natDegree_C_mul_le _ _)).trans ?_
          simp
        simp only [hi, ↓reduceIte]
        split_ifs <;> omega
    have hlt : (if Q' j = 0 then 0 else (Q' j).natDegree + 1) <
        (if Q j = 0 then 0 else (Q j).natDegree + 1) := by
      simp only [hj, ↓reduceIte]
      split_ifs with h0
      · omega
      · have hQ'j : Q' j = C (ν j) * (taylor 1 (Q j) - Q j) := by
          simp only [hQ', mul_sub]
        have hD : taylor 1 (Q j) - Q j ≠ 0 := by
          intro hD
          apply h0
          rw [hQ'j, hD, mul_zero]
        have hdeg : (taylor 1 (Q j) - Q j).degree < (Q j).degree := by
          have := degree_sub_lt_left (degree_taylor (Q j) 1) (mt (taylor_eq_zero 1 (Q j)).1 hj)
            (leadingCoeff_taylor 1 (Q j))
          rwa [degree_taylor] at this
        have := natDegree_lt_natDegree hD hdeg
        have h2 : (Q' j).natDegree ≤ (taylor 1 (Q j) - Q j).natDegree := by
          rw [hQ'j]
          exact natDegree_C_mul_le _ _
        omega
    have hsum : ∑ i, (if Q' i = 0 then 0 else (Q' i).natDegree + 1) ≤ N := by
      have := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hle i)
        ⟨j, Finset.mem_univ j, hlt⟩
      omega
    have hQ'0 := ih Q' hsum h'
    -- the coefficient polynomials other than `Q j` vanish
    have hother : ∀ i, i ≠ j → Q i = 0 := by
      intro i hij
      by_contra hi
      have heq : C (ν i) * taylor 1 (Q i) = C (ν j) * Q i := sub_eq_zero.1 (hQ'0 i)
      have hlc := congrArg leadingCoeff heq
      simp only [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_taylor] at hlc
      exact hij (hν (mul_right_cancel₀ (leadingCoeff_ne_zero.2 hi) hlc))
    -- hence `Q j` vanishes at every natural number
    have hroot : ∀ k : ℕ, (Q j).IsRoot (k : K) := by
      intro k
      have hk := h k
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [hother i hij, eval_zero, mul_zero])
        (fun hj' => absurd (Finset.mem_univ j) hj')] at hk
      exact (mul_eq_zero.1 hk).resolve_left (pow_ne_zero _ (hν0 j))
    apply hj
    refine eq_zero_of_infinite_isRoot _ ((Set.infinite_range_of_injective
      Nat.cast_injective).mono ?_)
    rintro _ ⟨k, rfl⟩
    exact hroot k

/-- Independence of exponential polynomials in characteristic zero: if the `ν i` are distinct
and nonzero and `∑ i, ν i ^ k * Q i (k) = 0` for every `k : ℕ`, then every coefficient
polynomial `Q i` is zero. -/
theorem eq_zero_of_sum_pow_mul_eval_eq_zero {ν : ι → K} (hν : Function.Injective ν)
    (hν0 : ∀ i, ν i ≠ 0) {Q : ι → K[X]}
    (h : ∀ k : ℕ, ∑ i, ν i ^ k * (Q i).eval (k : K) = 0) : ∀ i, Q i = 0 :=
  eq_zero_of_sum_pow_mul_eval_eq_zero_of_le hν hν0 _ Q le_rfl h

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
