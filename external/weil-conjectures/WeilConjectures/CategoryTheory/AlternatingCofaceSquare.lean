/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! # The signed coface identity without degeneracies

Source: Stacks Project, Tag 0194. Only the coface relations are needed for the
alternating differential to square to zero. The proof pairs two ways of deleting
two positions, exactly as in Mathlib's alternating face-map complex.
(blueprint: new-finite-cover-alternating-coface-square)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Preadditive

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- Double-deletion cancellation for a system of cofaces, without degeneracies.
Source: Stacks Project, Tag 0194. Partition pairs `(i,j)` according to `j ≤ i`.
The bijection `(i,j) ↦ (j,i+1)` pairs every term in the first part with a term
in the complement. The coface identity identifies their composites and the
incremented index reverses the sign, so the two sums cancel.
(blueprint: new-finite-cover-alternating-coface-square) -/
theorem alternatingCofaceSquare (A : ℕ → C)
    (δ : ∀ n : ℕ, Fin (n + 2) → (A n ⟶ A (n + 1)))
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3)) (h : j.val ≤ i.val),
      δ n i ≫ δ (n + 1) j =
        δ n (j.castLT (lt_of_le_of_lt h i.is_lt)) ≫ δ (n + 1) i.succ)
    (n : ℕ) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • δ n i) ≫
      (∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) • δ (n + 1) j) = 0 := by
  classical
  rw [sum_comp]
  simp only [comp_sum, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.is_lt),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg _root_.Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using
        congrArg Fin.castSucc (congrArg _root_.Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · intro hj
      subst hj
      simp at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    rw [hδ n i j (Finset.mem_filter.mp hij).2]
    congr 1
    simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_mul, neg_neg, mul_one,
      Fin.val_castLT]
    exact mul_comm _ _

end CategoryTheory
