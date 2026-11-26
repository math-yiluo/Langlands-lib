import Langlands.Global.RankinSelberg.RealTwoBlockEntries
import Langlands.LinearAlgebra.TriangularUnitary
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals

/-! # Forward and inverse matrices of the real right tail -/

noncomputable section

open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar

open Langlands.Archimedean (unitaryCompact)
open Langlands.ProductLeviChamber (twoBlock twoBlock_index_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "R" => fun n k => Matrix (Fin k) (Fin (n - k)) ℝ

variable {n k : ℕ} (hk : 0 < k) (hkn : k < n)

local notation "B" => twoBlock n k hk hkn

/-- Order-preserving indexing of the first and tail blocks combined. -/
def tailBlockIndex : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkn.le))

private theorem tailBlockIndex_left (i : Fin k) : tailBlockIndex hkn (Sum.inl i) = (B).index (0 : Fin 2) i := by
  apply Fin.ext
  rw [twoBlock_index_val]
  simp [tailBlockIndex, finSumFinEquiv_apply_left]

private theorem tailBlockIndex_right (i : Fin (n - k)) :
    tailBlockIndex hkn (Sum.inr i) = (B).index (1 : Fin 2) i := by
  apply Fin.ext
  rw [twoBlock_index_val]
  rfl

private theorem upperRectangle_blockMatrix (X : R n k) :
    (upperRectangle hk hkn X).val = Matrix.reindex (tailBlockIndex hkn) (tailBlockIndex hkn)
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) X 0 1) := by
  let e := tailBlockIndex hkn
  let u := (rectangleCoordinates hk hkn).symm X
  have hX : (B).radicalCoordinates ℝ u ⟨((0 : Fin 2), (1 : Fin 2)), by change (0 : ℕ) < 1; decide⟩ = X :=
    (rectangleCoordinates hk hkn).apply_symm_apply X
  have hd := ((B).mem_unipotentRadical_iff ℝ u.val).mp u.2
  have hl := ((B).mem_parabolic_iff ℝ u.val.val).mp u.val.2
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  change u.val.val.val (e i) (e j) =
    Matrix.reindex e e (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) X 0 1) (e i) (e j)
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa only [e, tailBlockIndex_left hk hkn, Matrix.fromBlocks_apply₁₁, Matrix.one_apply] using
      hd (0 : Fin 2) i j
  · simpa only [e, tailBlockIndex_left hk hkn, tailBlockIndex_right hk hkn,
      Matrix.fromBlocks_apply₁₂, (B).radicalCoordinates_apply] using congrFun (congrFun hX i) j
  · simpa only [e, tailBlockIndex_left hk hkn, tailBlockIndex_right hk hkn,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using hl (1 : Fin 2) (0 : Fin 2) i j (by change (0 : ℕ) < 1; decide)
  · simpa only [e, tailBlockIndex_right hk hkn, Matrix.fromBlocks_apply₂₂, Matrix.one_apply] using
      hd (1 : Fin 2) i j

private theorem diagonalBlocks_blockMatrix (g : G k) (h : G (n - k)) :
    (diagonalBlocks hk hkn g h).val = Matrix.reindex (tailBlockIndex hkn) (tailBlockIndex hkn)
      (Matrix.fromBlocks g.val 0 0 h.val) := by
  rw [realTwoBlockEntries n k hk hkn]
  let e := finCongr (Nat.add_sub_of_le hkn.le)
  let f : Fin k ⊕ Fin (n - k) ≃ Fin (k + (n - k)) := finSumFinEquiv
  change Matrix.reindex e e (Matrix.reindex f f (Matrix.fromBlocks g.val 0 0 h.val)) = _
  rw [← Equiv.trans_apply, Matrix.reindex_trans]
  rfl

/-- The two displayed block matrices give the right-tail chart and its inverse,
with the left unitary factor moved to the right in the inverse. -/
def RealGapTailMatrixStatement : Prop :=
  ∀ (n k : ℕ) (hk : 0 < k) (hkn : k < n) (h : G (n - k)) (X : R n k) (q : K n),
    let e := tailBlockIndex hkn
    let g := rightTail hk hkn h X q
    g.val = q.val.val * Matrix.reindex e e (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) X 0 h.val) ∧
      g⁻¹.val = Matrix.reindex e e (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ)
        (-(X * h⁻¹.val)) 0 h⁻¹.val) * q.val⁻¹.val

theorem realGapTailMatrix : RealGapTailMatrixStatement := by
  intro n k hk hkn h X q
  let e := tailBlockIndex hkn
  let A := Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) X 0 h.val
  let C := Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) (-(X * h⁻¹.val)) 0 h⁻¹.val
  let g := rightTail hk hkn h X q
  have hA : g.val = q.val.val * Matrix.reindex e e A := by
    unfold g rightTail
    rw [Units.val_mul, Units.val_mul, diagonalBlocks_blockMatrix, upperRectangle_blockMatrix,
      Matrix.mul_assoc]
    simp only [A, e, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Units.val_one, Matrix.fromBlocks_multiply,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hAC : A * C = 1 := by
    dsimp only [A, C]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, neg_add_cancel,
      h.mul_inv, Matrix.fromBlocks_one]
  have hInv : g.val * (Matrix.reindex e e C * q.val⁻¹.val) = 1 := by
    rw [hA, ← Matrix.mul_assoc, Matrix.mul_assoc q.val.val, Matrix.reindex_apply,
      Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hAC, Matrix.submatrix_one_equiv,
      Matrix.mul_one, q.val.mul_inv]
  change g.val = _ ∧ g⁻¹.val = _
  refine ⟨hA, ?_⟩
  calc
    g⁻¹.val = g⁻¹.val * 1 := (Matrix.mul_one _).symm
    _ = g⁻¹.val * (g.val * (Matrix.reindex e e C * q.val⁻¹.val)) := by rw [hInv]
    _ = _ := by rw [← Matrix.mul_assoc, g.inv_mul, Matrix.one_mul]

/-- The actual trailing columns of a matrix in the two-block indexing. -/
def tailColumns (g : G n) : Matrix (Fin n) (Fin (n - k)) ℝ :=
  fun i j => g.val i (tailBlockIndex hkn (Sum.inr j))

/-- The trailing columns control the additive norm of the tail and rectangle. The leading
columns are columns of the unitary factor, so they give a uniform contribution to the norm. -/
theorem rightTail_norm_bounds (h : G (n - k)) (X : R n k) (q : K n) :
    let g := rightTail hk hkn h X q
    ‖h.val‖ ≤ (n : ℝ) * ‖tailColumns hkn g‖ ∧
      ‖X‖ ≤ (n : ℝ) * ‖tailColumns hkn g‖ ∧ ‖g.val‖ ≤ 1 + ‖tailColumns hkn g‖ := by
  let e := tailBlockIndex hkn
  let g := rightTail hk hkn h X q
  let A := Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) X 0 h.val
  have hg : g.val = q.val.val * Matrix.reindex e e A := (realGapTailMatrix n k hk hkn h X q).1
  have hA : q.val⁻¹.val * g.val = Matrix.reindex e e A := by
    rw [hg, ← Matrix.mul_assoc, q.val.inv_mul, Matrix.one_mul]
  have hU (i j : Fin n) : ‖q.val.val i j‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup q.2 i j
  have hU' (i j : Fin n) : ‖q.val⁻¹.val i j‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup (q⁻¹ : K n).2 i j
  have hTail (i : Fin n) (j : Fin (n - k)) :
      ‖(Matrix.reindex e e A) i (e (Sum.inr j))‖ ≤ (n : ℝ) * ‖tailColumns hkn g‖ := by
    rw [← hA, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ : Fin n, ‖tailColumns hkn g‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul, ← one_mul ‖tailColumns hkn g‖]
        exact mul_le_mul (hU' i l) (Matrix.norm_entry_le_entrywise_sup_norm (tailColumns hkn g))
          (norm_nonneg _) zero_le_one
      _ = _ := by simp [nsmul_eq_mul]
  have hFirst (i : Fin n) (j : Fin k) : (Matrix.reindex e e A) i (e (Sum.inl j)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i (e (Sum.inl j)) := by
    obtain ⟨i, rfl⟩ := e.surjective i
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.one_apply, e.injective.eq_iff]
    cases i <;> simp [A, Matrix.one_apply]
  change ‖h.val‖ ≤ _ ∧ ‖X‖ ≤ _ ∧ ‖g.val‖ ≤ _
  refine ⟨(Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_,
    (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_, (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_⟩
  · simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      A, Matrix.fromBlocks_apply₂₂] using hTail (e (Sum.inr i)) j
  · simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      A, Matrix.fromBlocks_apply₁₂] using hTail (e (Sum.inl i)) j
  · obtain ⟨j, rfl⟩ := e.surjective j
    rcases j with j | j
    · have he : g.val i (e (Sum.inl j)) = q.val.val i (e (Sum.inl j)) := by
        rw [hg, Matrix.mul_apply]
        simp_rw [hFirst]
        rw [← Matrix.mul_apply, Matrix.mul_one]
      rw [he]
      exact (hU i _).trans (le_add_of_nonneg_right (norm_nonneg _))
    · exact (Matrix.norm_entry_le_entrywise_sup_norm (tailColumns hkn g) (i := i) (j := j)).trans
        (le_add_of_nonneg_left zero_le_one)

/-- The absolute determinant of the whole right tail is exactly that of the tail group variable. -/
theorem realNormalizedAbs_det_rightTail (h : G (n - k)) (X : R n k) (q : K n) :
    ArchimedeanLocal.realNormalizedAbs (rightTail hk hkn h X q).val.det =
      ArchimedeanLocal.realNormalizedAbs h.val.det := by
  have hg := (realGapTailMatrix n k hk hkn h X q).1
  dsimp only at hg
  have hq : |q.val.val.det| = 1 := by
    have hu := Matrix.det_of_mem_unitary q.2
    have h2 : q.val.val.det * q.val.val.det = 1 := by
      simpa only [star_trivial] using Unitary.star_mul_self_of_mem hu
    apply (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by decide : 2 ≠ 0)).mp
    rw [sq_abs, sq, h2]
  rw [hg, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul]
  simp only [ArchimedeanLocal.realNormalizedAbs, abs_mul, hq, one_mul]

end Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar
