import Langlands.Global.RankinSelberg.RealGapOrdinaryMajorant
import Langlands.Global.RankinSelberg.RealGodementLowerRectangle

/-! # Leading and tail columns of the lower rectangle in the real gap kernel -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapSplitTestColumns

open Langlands.GeneralLinear (lowerBlockPair reindex)
open RealGodementLowerRectangle (lowerRectangle)
open RealGapLeadingSchwartz (leadingStack)
open RealGapOrdinaryMajorant (leadingInput)
open RealTwoBlockHaar (tailBlockIndex tailColumns diagonalBlocks realTwoBlockEntries)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ

/-- The first block of columns in the combined block indexing. -/
def leadingColumns {n k : ℕ} (hkn : k < n) (g : G n) : Mat n k :=
  fun i j => g.val i (tailBlockIndex hkn (Sum.inl j))

private theorem leadingInput_apply_cast {n k d : ℕ} (e : k + d = n)
    (A : Mat k k) (Y : Mat d k) (i : Fin (k + d)) (j : Fin k) :
    leadingInput e A Y (finCongr e i) j = leadingStack A Y i j := by
  subst n
  rfl

private theorem lowerRectangle_product {r t : ℕ} (h : t < r) (g : G (t + 1))
    (Y : Mat (r + 1 - (t + 1)) (t + 1)) :
    diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) g 1 * lowerRectangle h Y =
      reindex (finCongr (Nat.add_sub_of_le (Nat.succ_le_succ h.le))) (lowerBlockPair g Y 1) := by
  rw [realTwoBlockEntries, lowerRectangle, ← map_mul]
  have hl := Unfolding.lowerBlockPair_mul_left g 1 Y 1
  rw [mul_one] at hl
  rw [hl]
  rfl

/-- Multiplication by the embedded leading matrix and lower rectangle replaces the leading
columns with the multiplied stack and leaves the trailing columns unchanged. -/
def RealGapSplitTestColumnsStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (B : G (r + 1)) (z : G (t + 1))
      (Y : Mat (r + 1 - (t + 1)) (t + 1)),
    let hk := Nat.succ_pos t
    let he := Nat.succ_lt_succ h
    let C := B * diagonalBlocks hk he z 1 * lowerRectangle h Y
    leadingColumns he C = B.val * leadingInput (Nat.add_sub_of_le he.le) z.val Y ∧
      tailColumns he C = tailColumns he B

theorem realGapSplitTestColumns : RealGapSplitTestColumnsStatement := by
  intro r t h B z Y
  let hk := Nat.succ_pos t
  let he := Nat.succ_lt_succ h
  let d := r + 1 - (t + 1)
  let ι := tailBlockIndex he
  let e := Nat.add_sub_of_le he.le
  let b := diagonalBlocks hk he z 1 * lowerRectangle h Y
  have hb : b.val = Matrix.reindex ι ι (Matrix.fromBlocks z.val 0 Y 1) := by
    unfold b
    rw [lowerRectangle_product]
    change Matrix.reindex (finCongr e) (finCongr e)
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks z.val 0 Y 1)) = _
    rw [← Equiv.trans_apply, Matrix.reindex_trans]
    rfl
  have h₁ (i : Fin (r + 1)) (j : Fin (t + 1)) : b.val i (ι (Sum.inl j)) =
      leadingInput e z.val Y i j := by
    obtain ⟨i, rfl⟩ := ι.surjective i
    rw [hb, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · change _ = leadingInput e z.val Y (finCongr e (i.castAdd d)) j
      rw [leadingInput_apply_cast, leadingStack, Fin.append_left, Matrix.fromBlocks_apply₁₁]
    · change _ = leadingInput e z.val Y (finCongr e (i.natAdd (t + 1))) j
      rw [leadingInput_apply_cast, leadingStack, Fin.append_right, Matrix.fromBlocks_apply₂₁]
  have h₂ (i : Fin (r + 1)) (j : Fin d) : b.val i (ι (Sum.inr j)) =
      (1 : Mat (r + 1) (r + 1)) i (ι (Sum.inr j)) := by
    obtain ⟨i, rfl⟩ := ι.surjective i
    rw [hb, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      Matrix.one_apply]
    simp only [ι.injective.eq_iff]
    rcases i with i | i <;> simp [Matrix.one_apply]
  change leadingColumns he (B * diagonalBlocks hk he z 1 * lowerRectangle h Y) = _ ∧
    tailColumns he (B * diagonalBlocks hk he z 1 * lowerRectangle h Y) = _
  rw [mul_assoc]
  constructor
  · ext i j
    change (B.val * b.val) i (ι (Sum.inl j)) = _
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => congrArg (B.val i l * ·) (h₁ l j)
  · ext i j
    change (B.val * b.val) i (ι (Sum.inr j)) = B.val i (ι (Sum.inr j))
    rw [Matrix.mul_apply]
    simp_rw [h₂]
    rw [← Matrix.mul_apply, Matrix.mul_one]

end Langlands.Global.RankinSelbergGlobal.RealGapSplitTestColumns
