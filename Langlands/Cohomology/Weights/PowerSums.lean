import Langlands.Cohomology.Weights.SeparationProof
import Mathlib.LinearAlgebra.Lagrange

/-! # Power sums and the alternating characteristic rational function -/

noncomputable section

open Polynomial
open scoped BigOperators Classical

set_option autoImplicit false

namespace Langlands.Cohomology.Weights

/-- The sum of the `k`th powers of the roots, with multiplicity, in the coefficient field. -/
def rootPowerSum {K : Type*} [Field K] (P : K[X]) (k : ℕ) : K :=
  (P.roots.map fun x => x ^ k).sum

@[simp] theorem rootPowerSum_one {K : Type*} [Field K] (k : ℕ) :
    rootPowerSum (1 : K[X]) k = 0 := by
  simp [rootPowerSum]

theorem rootPowerSum_mul {K : Type*} [Field K] {P Q : K[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (k : ℕ) :
    rootPowerSum (P * Q) k = rootPowerSum P k + rootPowerSum Q k := by
  simp [rootPowerSum, roots_mul (mul_ne_zero hP hQ)]

theorem rootPowerSum_pow {K : Type*} [Field K] (P : K[X]) (m k : ℕ) :
    rootPowerSum (P ^ m) k = (m : K) * rootPowerSum P k := by
  simp [rootPowerSum, roots_pow, Multiset.map_nsmul, Multiset.sum_nsmul]

private theorem sum_map_eq_sum_count {K : Type*} [Field K] (s : Multiset K)
    (S : Finset K) (hS : s.toFinset ⊆ S) (f : K → K) :
    (s.map f).sum = ∑ z ∈ S, (s.count z : K) * f z := by
  rw [Finset.sum_multiset_map_count]
  simp_rw [nsmul_eq_mul]
  exact Finset.sum_subset hS (fun z _ hz => by
    rw [Multiset.count_eq_zero.mpr (by simpa using hz), Nat.cast_zero, zero_mul])

/-- Two finite multisets of nonzero elements in a characteristic-zero field agree if their
power sums agree for all sufficiently large exponents. -/
theorem multiset_eq_of_eventual_powerSums_eq {K : Type*} [Field K] [CharZero K]
    {s t : Multiset K} (hs : (0 : K) ∉ s) (ht : (0 : K) ∉ t) {N : ℕ}
    (h : ∀ k ≥ N, (s.map (fun x => x ^ k)).sum = (t.map (fun x => x ^ k)).sum) : s = t := by
  let S := s.toFinset ∪ t.toFinset
  let c : K → K := fun z => (s.count z : K) - (t.count z : K)
  have hpow (k : ℕ) : ∑ z ∈ S, c z * z ^ (k + N) = 0 := by
    have heq := h (k + N) (Nat.le_add_left N k)
    rw [sum_map_eq_sum_count s S Finset.subset_union_left,
      sum_map_eq_sum_count t S Finset.subset_union_right] at heq
    simpa only [c, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using heq
  have heval (Q : K[X]) : ∑ z ∈ S, (c z * z ^ N) * Q.eval z = 0 := by
    induction Q using Polynomial.induction_on' with
    | add Q R hQ hR =>
      simp only [eval_add, mul_add, Finset.sum_add_distrib, hQ, hR, add_zero]
    | monomial k a =>
      have hf (z : K) : (c z * z ^ N) * (monomial k a).eval z = a * (c z * z ^ (k + N)) := by
        simp only [eval_monomial, pow_add]
        ring
      simp only [hf, ← Finset.mul_sum, hpow, mul_zero]
  refine Multiset.ext' fun z => ?_
  by_cases hz : z ∈ S
  · have hz0 : z ≠ 0 := by
      rintro rfl
      simp [S, hs, ht] at hz
    have hL := heval (Lagrange.basis S id z)
    rw [Finset.sum_eq_single z (fun x hx hxz => ?_) (fun h => (h hz).elim)] at hL
    · have he : (Lagrange.basis S id z).eval z = 1 :=
        Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hz
      rw [he, mul_one] at hL
      have hcz : c z = 0 := (mul_eq_zero.mp hL).resolve_right (pow_ne_zero _ hz0)
      exact_mod_cast (sub_eq_zero.mp hcz)
    · have he : (Lagrange.basis S id z).eval x = 0 :=
        Lagrange.eval_basis_of_ne (v := id) hxz.symm hx
      rw [he, mul_zero]
  · have hsz : z ∉ s := fun h => hz (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr h))
    have htz : z ∉ t := fun h => hz (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr h))
    rw [Multiset.count_eq_zero.mpr hsz, Multiset.count_eq_zero.mpr htz]

/-- Monic complex polynomials with nonzero constant term are determined by their power sums
at all sufficiently large exponents. -/
theorem eq_of_monic_of_eventual_rootPowerSum_eq {P Q : ℂ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hP0 : P.eval 0 ≠ 0) (hQ0 : Q.eval 0 ≠ 0) {N : ℕ}
    (h : ∀ k ≥ N, rootPowerSum P k = rootPowerSum Q k) : P = Q :=
  eq_of_monic_of_roots_eq hP hQ
    (multiset_eq_of_eventual_powerSums_eq (fun h => hP0 ((mem_roots hP.ne_zero).1 h))
      (fun h => hQ0 ((mem_roots hQ.ne_zero).1 h)) h)

private theorem rootPowerSum_prod {ι : Type*} (s : Finset ι) (H : ι → ℂ[X])
    (hH : ∀ i ∈ s, (H i).Monic) (k : ℕ) :
    rootPowerSum (∏ i ∈ s, H i) k = ∑ i ∈ s, rootPowerSum (H i) k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hm : ∀ j ∈ s, (H j).Monic := fun j hj => hH j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, rootPowerSum_mul
      (hH i (Finset.mem_insert_self i s)).ne_zero (monic_prod_of_monic _ _ hm).ne_zero, ih hm]

/-- Kottwitz §5, passage from (5.5) to (5.6): eventual equality of the signed power sums
implies the alternating characteristic rational-function identity. No purity or semisimplicity
assumption is needed; the monic polynomials have nonzero constant terms. -/
theorem alternatingPolynomial_eq_zpow_of_eventual_powerSums {d : ℕ} {a : ℤ}
    {H : Fin (2 * d + 1) → ℂ[X]} {P : ℂ[X]} (hH : ∀ i, (H i).Monic)
    (hH0 : ∀ i, (H i).eval 0 ≠ 0) (hP : P.Monic) (hP0 : P.eval 0 ≠ 0) {N : ℕ}
    (h : ∀ k ≥ N, ∑ i, (-1 : ℂ) ^ i.val * rootPowerSum (H i) k =
      (a : ℂ) * rootPowerSum P k) :
    alternatingPolynomial d H = (algebraMap ℂ[X] (RatFunc ℂ) P) ^ a := by
  let s := Finset.univ.filter (fun i : Fin (2 * d + 1) => Even i.val)
  let t := Finset.univ.filter (fun i : Fin (2 * d + 1) => ¬ Even i.val)
  let E := ∏ i ∈ s, H i
  let O := ∏ i ∈ t, H i
  have hEm : E.Monic := monic_prod_of_monic _ _ (fun i _ => hH i)
  have hOm : O.Monic := monic_prod_of_monic _ _ (fun i _ => hH i)
  have hE0 : E.eval 0 ≠ 0 := by
    rw [show E = ∏ i ∈ s, H i from rfl, eval_prod]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hH0 i
  have hO0 : O.eval 0 ≠ 0 := by
    rw [show O = ∏ i ∈ t, H i from rfl, eval_prod]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hH0 i
  have htrace (k : ℕ) (hk : N ≤ k) : rootPowerSum E k - rootPowerSum O k =
      (a : ℂ) * rootPowerSum P k := by
    rw [rootPowerSum_prod s H (fun i _ => hH i), rootPowerSum_prod t H (fun i _ => hH i)]
    rw [← h k hk, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (2 * d + 1) => Even i.val), sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2.neg_one_pow, one_mul]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2).neg_one_pow, neg_one_mul]
  rw [alternatingPolynomial_eq_div]
  change algebraMap ℂ[X] (RatFunc ℂ) E / algebraMap ℂ[X] (RatFunc ℂ) O = _
  have hO' := RatFunc.algebraMap_ne_zero (K := ℂ) hOm.ne_zero
  have hP' := RatFunc.algebraMap_ne_zero (K := ℂ) hP.ne_zero
  rcases Int.natAbs_eq a with ha | ha
  · have heq : E = P ^ a.natAbs * O := by
      apply eq_of_monic_of_eventual_rootPowerSum_eq hEm ((hP.pow _).mul hOm) hE0
        (by rw [eval_mul, eval_pow]; exact mul_ne_zero (pow_ne_zero _ hP0) hO0)
      intro k hk
      rw [rootPowerSum_mul (pow_ne_zero _ hP.ne_zero) hOm.ne_zero, rootPowerSum_pow]
      have he := htrace k hk
      have hcast : (a : ℂ) = (a.natAbs : ℂ) := by
        simpa only [Int.cast_natCast] using congrArg (fun m : ℤ => (m : ℂ)) ha
      rw [hcast] at he
      exact (sub_eq_iff_eq_add.mp he)
    rw [ha, zpow_natCast, heq, map_mul, map_pow, mul_div_cancel_right₀ _ hO']
  · have heq : E * P ^ a.natAbs = O := by
      apply eq_of_monic_of_eventual_rootPowerSum_eq (hEm.mul (hP.pow _)) hOm
        (by rw [eval_mul, eval_pow]; exact mul_ne_zero hE0 (pow_ne_zero _ hP0)) hO0
      intro k hk
      rw [rootPowerSum_mul hEm.ne_zero (pow_ne_zero _ hP.ne_zero), rootPowerSum_pow]
      have he := htrace k hk
      rw [show (a : ℂ) = -(a.natAbs : ℂ) from by exact_mod_cast ha, neg_mul] at he
      linear_combination he
    have heq' := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) heq
    rw [map_mul, map_pow] at heq'
    rw [ha, zpow_neg, zpow_natCast, div_eq_iff hO', ← heq', mul_left_comm,
      inv_mul_cancel₀ (pow_ne_zero _ hP'), mul_one]

end Langlands.Cohomology.Weights
