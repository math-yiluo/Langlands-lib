import Langlands.Representation.Exponents.PositiveRootBlockSumsStatement
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-! Finite cancellation and actual-coordinate reindexing for positive roots. -/

noncomputable section

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeRegularComparison
open scoped BigOperators

namespace PositiveRootBlockSumsProof

private theorem adjacent_sum {m : ℕ} (A : BlockShape m)
    (c : ℝ) (j : Fin (A.length - 1)) :
    ∑ k : Fin A.length, (A.size k : ℝ) *
      (c * ((if k.val = j.val then (1 : ℝ) / A.size k else 0) -
        (if k.val = j.val + 1 then (1 : ℝ) / A.size k else 0))) = 0 := by
  classical
  let j₀ : Fin A.length := ⟨j.val, by have := j.isLt; omega⟩
  let j₁ : Fin A.length := ⟨j.val + 1, by have := j.isLt; omega⟩
  calc
    _ = ∑ k : Fin A.length,
        ((if k = j₀ then c else 0) - (if k = j₁ then c else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      have hd : (A.size k : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (A.positive k))
      have h₀ : k.val = j.val ↔ k = j₀ := by
        constructor
        · exact fun h => Fin.ext h
        · exact fun h => congrArg Fin.val h
      have h₁ : k.val = j.val + 1 ↔ k = j₁ := by
        constructor
        · exact fun h => Fin.ext h
        · exact fun h => congrArg Fin.val h
      simp only [h₀, h₁]
      split_ifs <;> field_simp [hd] <;> ring
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      simp

theorem weighted_sum {n : ℕ} (D : BlockShape n) (R : BlockRefinement D)
    (v : Fin (D.flatten R).length → ℝ)
    (hv : IsPositiveRootParameter D R v) (i : Fin D.length) :
    ∑ k : Fin (R i).length,
      ((R i).size k : ℝ) * v (D.flattenBlockEquiv R ⟨i, k⟩) = 0 := by
  classical
  obtain ⟨c, _, hexp⟩ := hv
  calc
    _ = ∑ k : Fin (R i).length, ∑ j : Fin ((R i).length - 1),
        ((R i).size k : ℝ) *
          (c i j * ((if k.val = j.val then (1 : ℝ) / (R i).size k else 0) -
            (if k.val = j.val + 1 then (1 : ℝ) / (R i).size k else 0))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hexp i k, Finset.mul_sum]
    _ = ∑ j : Fin ((R i).length - 1), ∑ k : Fin (R i).length,
        ((R i).size k : ℝ) *
          (c i j * ((if k.val = j.val then (1 : ℝ) / (R i).size k else 0) -
            (if k.val = j.val + 1 then (1 : ℝ) / (R i).size k else 0))) :=
      Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun j _ => adjacent_sum (R i) (c i j) j

theorem middle_sum {n : ℕ} (D : BlockShape n) (R : BlockRefinement D)
    (v : Fin (D.flatten R).length → ℝ)
    (hv : IsPositiveRootParameter D R v) (i : Fin D.length) :
    ∑ a : Fin (D.size i),
      v (blockIndex (D.flatten R) (D.index i a)) = 0 := by
  classical
  rw [← (R i).indexEquiv.sum_comp, Fintype.sum_sigma]
  change (∑ k : Fin (R i).length, ∑ b : Fin ((R i).size k),
    v (blockIndex (D.flatten R) (D.index i ((R i).index k b)))) = 0
  have hblock (k : Fin (R i).length) (b : Fin ((R i).size k)) :
      blockIndex (D.flatten R) (D.index i ((R i).index k b)) =
        D.flattenBlockEquiv R ⟨i, k⟩ := by
    rw [D.index_index_eq_flatten R ⟨i, k⟩ b, blockIndex_index]
  simp_rw [hblock]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    using weighted_sum D R v hv i

/-- Literal block-shape equality preserves the expanded parameter vector. -/
theorem transport_blockIndex {n : ℕ} {C C' : BlockShape n}
    (h : C = C') (v : Fin C.length → ℝ) (a : Fin n) :
    (h ▸ v) (blockIndex C' a) = v (blockIndex C a) := by
  subst C'
  rfl

theorem coarse_sum {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
    (h : (B.flatten Q).flatten R = B.flatten S)
    (v : Fin ((B.flatten Q).flatten R).length → ℝ)
    (hv : IsPositiveRootParameter (B.flatten Q) R v) (i : Fin B.length) :
    ∑ a : Fin (B.size i),
      (h ▸ v) (blockIndex (B.flatten S) (B.index i a)) = 0 := by
  classical
  simp_rw [transport_blockIndex h v]
  rw [← (Q i).indexEquiv.sum_comp, Fintype.sum_sigma]
  change (∑ j : Fin (Q i).length, ∑ b : Fin ((Q i).size j),
    v (blockIndex ((B.flatten Q).flatten R)
      (B.index i ((Q i).index j b)))) = 0
  apply Finset.sum_eq_zero
  intro j _
  simp_rw [B.index_index_eq_flatten Q ⟨i, j⟩]
  calc
    _ = ∑ a : Fin ((B.flatten Q).size (B.flattenBlockEquiv Q ⟨i, j⟩)),
        v (blockIndex ((B.flatten Q).flatten R)
          ((B.flatten Q).index (B.flattenBlockEquiv Q ⟨i, j⟩) a)) := by
      simpa only [finCongr_apply] using
        (finCongr (B.flatten_size_flattenBlockEquiv Q ⟨i, j⟩).symm).sum_comp
          (fun a => v (blockIndex ((B.flatten Q).flatten R)
            ((B.flatten Q).index (B.flattenBlockEquiv Q ⟨i, j⟩) a)))
    _ = 0 := middle_sum (B.flatten Q) R v hv (B.flattenBlockEquiv Q ⟨i, j⟩)

end PositiveRootBlockSumsProof

/-- The existing weighted positive-root condition has zero sums on actual blocks. -/
theorem positiveRootBlockSums : PositiveRootBlockSumsStatement :=
  ⟨fun _ D R v hv i => PositiveRootBlockSumsProof.weighted_sum D R v hv i,
    fun _ D R v hv i => PositiveRootBlockSumsProof.middle_sum D R v hv i,
    fun _ B Q R S h v hv i =>
      PositiveRootBlockSumsProof.coarse_sum B Q R S h v hv i⟩

end Langlands.Exponents
