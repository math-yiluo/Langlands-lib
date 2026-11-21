import Langlands.Global.RankinSelberg.ComplexTwoBlockRightHaar
import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices
import Langlands.Group.GL.RankMaps

/-! # Matrix entries of the complex two-block Haar coordinates -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexTwoBlockHaar

open Langlands.ProductLeviChamber (twoBlock twoBlock_index_val)
open Langlands.GeneralLinear (blockSum reindex determinant inverseTranspose
  blockSum_apply_left blockSum_apply_right blockSum_apply_left_right blockSum_apply_right_left)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Sq" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "Rect" => fun n k => Matrix (Fin k) (Fin (n - k)) ℂ

variable {n k : ℕ} (hk : 0 < k) (hkn : k < n)

local notation "B" => twoBlock n k hk hkn
local notation "L" => Langlands.GeneralLinear.BlockShape.Levi (twoBlock n k hk hkn) ℂ
local notation "e" => finCongr (Nat.add_sub_of_le hkn.le)

private theorem index_first (i : Fin k) : (B).index (0 : Fin 2) i = e (i.castAdd (n - k)) := by
  apply Fin.ext
  rw [twoBlock_index_val]
  simp

private theorem index_second (i : Fin (n - k)) : (B).index (1 : Fin 2) i = e (i.natAdd k) := by
  apply Fin.ext
  rw [twoBlock_index_val]
  rfl

/-- The diagonal blocks of the Haar chart are the standard consecutive matrix blocks. -/
def ComplexTwoBlockEntriesStatement : Prop :=
  ∀ (n k : ℕ) (hk : 0 < k) (hkn : k < n) (g₁ : G k) (g₂ : G (n - k)),
    diagonalBlocks hk hkn g₁ g₂ =
      reindex (finCongr (Nat.add_sub_of_le hkn.le)) (blockSum (g₁, g₂))

theorem complexTwoBlockEntries : ComplexTwoBlockEntriesStatement := by
  intro n k hk hkn g₁ g₂
  let S := twoBlock n k hk hkn
  let cast := finCongr (Nat.add_sub_of_le hkn.le)
  let m := (leviBlocks hk hkn).symm (g₁, g₂)
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := cast.surjective i
  obtain ⟨j, rfl⟩ := cast.surjective j
  change (S.leviEmbedding ℂ m).val (cast i) (cast j) =
    Matrix.reindex cast cast (blockSum (g₁, g₂)).val (cast i) (cast j)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine Fin.addCases (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [← index_first hk hkn, ← index_first hk hkn, S.leviEmbedding_apply_same, blockSum_apply_left]
    rfl
  · rw [← index_first hk hkn, ← index_second hk hkn,
      S.leviEmbedding_apply_ne ℂ m (i := (0 : Fin 2)) (j := (1 : Fin 2))
        i₀ j₁ (show (0 : Fin 2) ≠ 1 by decide), blockSum_apply_left_right]
  · rw [← index_second hk hkn, ← index_first hk hkn,
      S.leviEmbedding_apply_ne ℂ m (i := (1 : Fin 2)) (j := (0 : Fin 2))
        i₁ j₀ (show (1 : Fin 2) ≠ 0 by decide), blockSum_apply_right_left]
  · rw [← index_second hk hkn, ← index_second hk hkn, S.leviEmbedding_apply_same, blockSum_apply_right]
    rfl

/-- The upper-left factor in the Haar chart is the padding in the unequal-rank integral. -/
theorem diagonalBlocks_eq_padGL (g : G k) :
    diagonalBlocks hk hkn g 1 = padGL hkn.le g := by
  rw [complexTwoBlockEntries n k hk hkn]
  rfl

/-- The determinant of the chart's diagonal matrix is the product of the two determinants. -/
theorem determinant_diagonalBlocks (g₁ : G k) (g₂ : G (n - k)) :
    determinant (diagonalBlocks hk hkn g₁ g₂) = determinant g₁ * determinant g₂ := by
  rw [complexTwoBlockEntries n k hk hkn]
  apply Units.ext
  change Matrix.det (Matrix.reindex e e (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g₁.val 0 0 g₂.val))) = g₁.val.det * g₂.val.det
  rw [Matrix.det_reindex_self, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- Inverse transpose applies independently to the two blocks. -/
theorem inverseTranspose_diagonalBlocks (g₁ : G k) (g₂ : G (n - k)) :
    inverseTranspose n ℂ (diagonalBlocks hk hkn g₁ g₂) =
      diagonalBlocks hk hkn (inverseTranspose k ℂ g₁) (inverseTranspose (n - k) ℂ g₂) := by
  simp only [complexTwoBlockEntries n k hk hkn]
  apply Units.ext
  change (Matrix.reindex e e (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks g₁⁻¹.val 0 0 g₂⁻¹.val))).transpose =
    Matrix.reindex e e (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks g₁⁻¹.val.transpose 0 0 g₂⁻¹.val.transpose))
  rw [Matrix.transpose_reindex, Matrix.transpose_reindex, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_zero]

/-- The last row of left multiplication by an embedded first block is unchanged. -/
theorem lastRow_diagonalBlocks_mul {r : ℕ} (hkr : k < r + 1) (g : G k) (x : G (r + 1)) :
    (diagonalBlocks hk hkr g 1 * x).val (Fin.last r) = x.val (Fin.last r) := by
  rw [diagonalBlocks_eq_padGL]
  funext j
  exact UnequalAnalytic.mul_apply_of_row _
    (UnequalAnalytic.padGL_row hkr.le g (Fin.last r) (by simpa using Nat.le_of_lt_succ hkr)) j

end Langlands.Global.RankinSelbergGlobal.ComplexTwoBlockHaar
