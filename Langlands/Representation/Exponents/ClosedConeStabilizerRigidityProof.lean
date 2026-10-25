import Langlands.Representation.Exponents.ClosedConeStabilizerRigidityStatement
import Langlands.Representation.Geometric.WeylUniquenessProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Proof of the internal closed-cone stabilizer criterion. -/

namespace Langlands.Exponents

open GeneralLinear Geometric Finset
open scoped BigOperators

private def coordinateExtend {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then x ⟨k, hk⟩ else 0

private theorem coordinateExtend_lt {n : ℕ} (x : Fin n → ℝ)
    {k : ℕ} (hk : k < n) : coordinateExtend x k = x ⟨k, hk⟩ := by
  simp [coordinateExtend, hk]

private theorem coordinateExtend_fin {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    coordinateExtend x i = x i :=
  coordinateExtend_lt x i.isLt

private theorem partialSum_eq_extended_sum {n : ℕ} (x : Fin n → ℝ)
    {k : ℕ} (hk : k ≤ n) :
    partialSum x k = ∑ i ∈ range k, coordinateExtend x i := by
  rw [partialSum, Finset.sum_filter]
  have heq : ∑ i : Fin n, (if (i : ℕ) < k then x i else 0) =
      ∑ i : Fin n,
        (fun j : ℕ => if j < k then coordinateExtend x j else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [coordinateExtend_fin]
  rw [heq, Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < k then coordinateExtend x j else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

private theorem closedCone_pairing_antitone {n : ℕ} {x : Fin n → ℝ}
    (hx : IsClosedPositiveRootCone x) (a : Fin n → ℝ) (ha : Antitone a) :
    0 ≤ ∑ i, a i * x i := by
  have hby := Finset.sum_range_by_parts (coordinateExtend a) (coordinateExtend x) n
  simp only [smul_eq_mul] at hby
  have hleft : ∑ i, a i * x i =
      ∑ i ∈ range n, coordinateExtend a i * coordinateExtend x i := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => coordinateExtend a i * coordinateExtend x i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coordinateExtend_fin, coordinateExtend_fin]
  have htotal : ∑ i ∈ range n, coordinateExtend x i = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (coordinateExtend x) n]
    simpa only [coordinateExtend_fin] using hx.1
  rw [hleft, hby, htotal, mul_zero, zero_sub, neg_nonneg]
  refine Finset.sum_nonpos fun i hi => ?_
  have hir : i < n - 1 := mem_range.mp hi
  have hi0 : i < n := by omega
  have hi1 : i + 1 < n := by omega
  rw [coordinateExtend_lt _ hi1, coordinateExtend_lt _ hi0,
    ← partialSum_eq_extended_sum x hi1.le]
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (ha (Fin.mk_le_mk.mpr (by omega))))
    (hx.2 (i + 1) (by omega) hi1)

private theorem block_pairing_zero {n : ℕ} (B : BlockShape n)
    (v : Fin n → ℝ) (t : Fin B.length → ℝ)
    (hv : ∀ i : Fin B.length, ∑ a : Fin (B.size i), v (B.index i a) = 0) :
    ∑ a, t (blockIndex B a) * v a = 0 := by
  rw [← B.indexEquiv.sum_comp, Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro i _
  have heq : ∀ j : Fin (B.size i),
      t (blockIndex B (B.indexEquiv ⟨i, j⟩)) * v (B.indexEquiv ⟨i, j⟩) =
        t i * v (B.index i j) := by
    intro j
    change t (blockIndex B (B.index i j)) * v (B.index i j) = _
    rw [blockIndex_index]
  simp_rw [heq]
  rw [← Finset.mul_sum, hv i, mul_zero]

/-- A fixed shifted vector and a cone inequality force a block stabilizer. -/
theorem closedConeStabilizerRigidity : ClosedConeStabilizerRigidityStatement := by
  intro n B v t w hv ht hx hfix
  let a : Fin n → ℝ := fun j => t (blockIndex B j)
  have ha : Antitone a := fun _ _ hij => ht.antitone (blockIndex_monotone B hij)
  have hav : ∑ j, a j * v j = 0 := block_pairing_zero B v t hv
  have hawv : 0 ≤ ∑ j, a j * v (w j) :=
    closedCone_pairing_antitone hx a ha
  have hdiff : ∀ j, a j - a (w j) = v j - v (w j) := by
    intro j
    have h := hfix j
    change v (w j) - a (w j) = v j - a j at h
    linarith
  have hpair : ∑ j, a j * (a j - a (w j)) ≤ 0 := by
    simp_rw [hdiff, mul_sub]
    rw [Finset.sum_sub_distrib, hav]
    linarith
  have hnorm : ∑ j, a (w j) ^ 2 = ∑ j, a j ^ 2 :=
    Equiv.sum_comp w (fun j => a j ^ 2)
  have hsquares : ∑ j, (a j - a (w j)) ^ 2 =
      2 * ∑ j, a j * (a j - a (w j)) := by
    calc
      ∑ j, (a j - a (w j)) ^ 2 =
          ∑ j, (a j ^ 2 + a (w j) ^ 2 - 2 * (a j * a (w j))) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ j, a j ^ 2) + (∑ j, a (w j) ^ 2) -
          2 * (∑ j, a j * a (w j)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * ∑ j, a j * (a j - a (w j)) := by
        rw [hnorm]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        simp_rw [← sq]
        ring
  have hsumzero : ∑ j, (a j - a (w j)) ^ 2 = 0 := by
    apply le_antisymm
    · rw [hsquares]
      linarith
    · exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hae : ∀ j, a (w j) = a j := by
    intro j
    have hz : (a j - a (w j)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k - a (w k)))).mp
        hsumzero j (Finset.mem_univ j)
    nlinarith [sq_nonneg (a j - a (w j))]
  refine ⟨?_, ?_⟩
  · change ∀ j, blockIndex B (w j) = blockIndex B j
    intro j
    exact ht.injective (hae j)
  · intro j
    have h := hfix j
    change v (w j) - a (w j) = v j - a j at h
    rw [hae j] at h
    linarith

end Langlands.Exponents
