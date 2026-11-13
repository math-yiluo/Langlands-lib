import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # The full shape of a vertex-transitive Cartan matrix with a positive left kernel -/

noncomputable section

universe u

open Finset

namespace Langlands.GroupScheme.AffineCartan

variable {ι : Type u} [Fintype ι]

/-- The entry-preserving permutations of an integer matrix act transitively on its indices. -/
def IsVertexTransitive (B : Matrix ι ι ℤ) : Prop :=
  ∀ i j, ∃ σ : Equiv.Perm ι, (∀ k l, B (σ k) (σ l) = B k l) ∧ σ i = j

/-- A vertex-transitive integer matrix with a positive left kernel has zero row sums. -/
theorem rowSum_eq_zero_of_isVertexTransitive (B : Matrix ι ι ℤ)
    (htrans : IsVertexTransitive B) (m : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hker : Matrix.vecMul m B = 0) (i : ι) : ∑ j, B i j = 0 := by
  classical
  let : Nonempty ι := ⟨i⟩
  have hrowc : ∀ k, ∑ j, B k j = ∑ j, B i j := by
    intro k
    obtain ⟨σ, hσB, hσ⟩ := htrans i k
    rw [← hσ, ← Equiv.sum_comp σ (B (σ i))]
    exact Finset.sum_congr rfl fun j _ => hσB i j
  have hmpos : 0 < ∑ k, m k :=
    Finset.sum_pos (fun k _ => hm k) Finset.univ_nonempty
  have h1 : ∑ j, ∑ k, m k * B k j = 0 :=
    Finset.sum_eq_zero fun j _ => by
      simpa [Matrix.vecMul, dotProduct] using congrFun hker j
  have h2 : ∑ j, ∑ k, m k * B k j = (∑ k, m k) * ∑ j, B i j := by
    calc
      ∑ j, ∑ k, m k * B k j = ∑ k, ∑ j, m k * B k j := Finset.sum_comm
      _ = ∑ k, m k * ∑ j, B i j :=
        Finset.sum_congr rfl fun k _ => by rw [← Finset.mul_sum, hrowc k]
      _ = (∑ k, m k) * ∑ j, B i j := by rw [Finset.sum_mul]
  rw [h2] at h1
  exact (mul_eq_zero.mp h1).resolve_left hmpos.ne'

/-- The column sums vanish under the same hypotheses. -/
theorem colSum_eq_zero_of_isVertexTransitive (B : Matrix ι ι ℤ)
    (htrans : IsVertexTransitive B) (m : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hker : Matrix.vecMul m B = 0) (j : ι) : ∑ i, B i j = 0 := by
  classical
  let : Nonempty ι := ⟨j⟩
  have hcolc : ∀ l, ∑ i, B i l = ∑ i, B i j := by
    intro l
    obtain ⟨σ, hσB, hσ⟩ := htrans j l
    rw [← hσ, ← Equiv.sum_comp σ (fun i => B i (σ j))]
    exact Finset.sum_congr rfl fun i _ => hσB i j
  have htot : ∑ l, ∑ i, B i l = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ =>
      rowSum_eq_zero_of_isVertexTransitive B htrans m hm hker i
  have h3 : ∑ l, ∑ i, B i l = (Fintype.card ι : ℤ) * ∑ i, B i j := by
    rw [Finset.sum_congr rfl fun l _ => hcolc l]
    simp [Finset.sum_const]
  rw [h3] at htot
  exact (mul_eq_zero.mp htot).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

private theorem offDiag_bound_of_rowSum_eq_zero (B : Matrix ι ι ℤ)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    (hrow : ∀ i, ∑ j, B i j = 0) (i j : ι) (hij : i ≠ j) :
    -2 ≤ B i j ∧ (B i j = -2 → ∀ k, k ≠ i → k ≠ j → B i k = 0) := by
  classical
  have hsplit : ∑ k, B i k = B i i + B i j + ∑ k ∈ (univ.erase i).erase j, B i k := by
    rw [add_assoc, Finset.add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩),
      Finset.add_sum_erase _ _ (mem_univ i)]
  have hnp : ∀ k ∈ (univ.erase i).erase j, B i k ≤ 0 := fun k hk =>
    hoff i k (Ne.symm (ne_of_mem_erase (mem_of_mem_erase hk)))
  have hrest := Finset.sum_nonpos hnp
  rw [hrow i, hdiag] at hsplit
  refine ⟨by linarith, fun h k hki hkj => ?_⟩
  have h0 : ∑ k ∈ (univ.erase i).erase j, B i k = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonpos hnp).mp h0 k
    (mem_erase.mpr ⟨hkj, mem_erase.mpr ⟨hki, mem_univ k⟩⟩)

private theorem reverse_eq_neg_two_of_row_col_zero (B : Matrix ι ι ℤ)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    (hsupp : ∀ i j, B i j = 0 → B j i = 0)
    (hrow : ∀ i, ∑ j, B i j = 0) (hcol : ∀ j, ∑ i, B i j = 0)
    (i j : ι) (hij : i ≠ j) (h : B i j = -2) : B j i = -2 := by
  classical
  have hz := (offDiag_bound_of_rowSum_eq_zero B hdiag hoff hrow i j hij).2 h
  have hsplit : ∑ k, B k i = B i i + B j i + ∑ k ∈ (univ.erase i).erase j, B k i := by
    have e1 := Finset.add_sum_erase (univ.erase i) (fun k => B k i)
      (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩)
    have e2 := Finset.add_sum_erase univ (fun k => B k i) (mem_univ i)
    beta_reduce at e1 e2
    linarith
  have h0 : ∑ k ∈ (univ.erase i).erase j, B k i = 0 := Finset.sum_eq_zero fun k hk =>
    hsupp _ _ (hz k (ne_of_mem_erase (mem_of_mem_erase hk)) (ne_of_mem_erase hk))
  rw [hcol i, hdiag, h0] at hsplit
  linarith

/-- The full matrix is symmetric; its off-diagonal entries are `0`, `-1` or `-2`,
and an edge labelled `-2` is an isolated two-vertex component. No block
nondegeneracy or connectedness hypothesis is needed. -/
theorem shape_of_isVertexTransitive (B : Matrix ι ι ℤ)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    (hsupp : ∀ i j, B i j = 0 → B j i = 0)
    (htrans : IsVertexTransitive B) (m : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hker : Matrix.vecMul m B = 0) :
    (∀ i j, B i j = B j i) ∧
      (∀ i j, i ≠ j → B i j = 0 ∨ B i j = -1 ∨ B i j = -2) ∧
      ∀ i j, i ≠ j → B i j = -2 →
        ∀ k, k ≠ i → k ≠ j → B i k = 0 ∧ B j k = 0 := by
  have hrow := rowSum_eq_zero_of_isVertexTransitive B htrans m hm hker
  have hcol := colSum_eq_zero_of_isVertexTransitive B htrans m hm hker
  have hbound := offDiag_bound_of_rowSum_eq_zero B hdiag hoff hrow
  have hreverse := reverse_eq_neg_two_of_row_col_zero B hdiag hoff hsupp hrow hcol
  have hsymm : ∀ i j, B i j = B j i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h1 := (hbound i j hij).1
    have h2 := (hbound j i (Ne.symm hij)).1
    have h3 := hoff i j hij
    have h4 := hoff j i (Ne.symm hij)
    have h5 := hsupp i j
    have h6 := hsupp j i
    have h7 := hreverse i j hij
    have h8 := hreverse j i (Ne.symm hij)
    omega
  refine ⟨hsymm, ?_, ?_⟩
  · intro i j hij
    have := (hbound i j hij).1
    have := hoff i j hij
    omega
  · intro i j hij h k hki hkj
    exact ⟨(hbound i j hij).2 h k hki hkj,
      (hbound j i (Ne.symm hij)).2 (hreverse i j hij h) k hkj hki⟩

end Langlands.GroupScheme.AffineCartan
