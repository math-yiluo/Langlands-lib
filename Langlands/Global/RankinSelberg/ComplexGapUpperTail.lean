import Langlands.Global.RankinSelberg.ComplexGapRectangleShear
import Langlands.Global.RankinSelberg.ComplexGapTriangularFourier
import Langlands.Group.GL.RankMaps

/-! # The upper block coordinates of the split tail -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapUpperTail

open Langlands.GeneralLinear (rankInclusion reindex)
open Langlands.GeneralLinear.UpperUnipotent (entry_diag entry_eq_zero)
open ComplexGapColumnFourier (directColumn transposeColumn)
open ComplexGapRectangleShear (firstRowCorrection)

variable (k q : ℕ)

local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (k + q + 1) ℂ
local notation "Head" => Fin k → ℂ
local notation "Tail" => Matrix (Fin k) (Fin q) ℂ
local notation "Rect" => Matrix (Fin k) J ℂ
local notation "blockIndices" => (finSumFinEquiv : Fin k ⊕ J ≃ I)

private def blockCoordinates (Y : Rect) (Z : N) : Matrix.GeneralLinearGroup (Fin k ⊕ J) ℂ where
  val := Matrix.fromBlocks 1 Y 0 Z.val.val
  inv := Matrix.fromBlocks 1 (-(Y * Z⁻¹.val.val)) 0 Z⁻¹.val.val
  val_inv := by
    have h : Z.val.val * Z⁻¹.val.val = (1 : Matrix J J ℂ) := Z.val.val_inv
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, neg_add_cancel, h, Matrix.fromBlocks_one]
  inv_val := by
    have h : Z⁻¹.val.val * Z.val.val = (1 : Matrix J J ℂ) := Z.val.inv_val
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_assoc, h, add_neg_cancel,
      Matrix.fromBlocks_one]

private def block (Y : Rect) (Z : N) : G :=
  reindex blockIndices (blockCoordinates k q Y Z)

private theorem block_top_left (Y : Rect) (Z : N) (i j : Fin k) :
    (block k q Y Z).val (i.castAdd (q + 1)) (j.castAdd (q + 1)) = (1 : Matrix (Fin k) (Fin k) ℂ) i j := by
  change Matrix.fromBlocks 1 Y 0 Z.val.val
    ((blockIndices).symm (i.castAdd (q + 1))) ((blockIndices).symm (j.castAdd (q + 1))) = _
  simp

private theorem block_top_right (Y : Rect) (Z : N) (i : Fin k) (j : J) :
    (block k q Y Z).val (i.castAdd (q + 1)) (j.natAdd k) = Y i j := by
  change Matrix.fromBlocks 1 Y 0 Z.val.val
    ((blockIndices).symm (i.castAdd (q + 1))) ((blockIndices).symm (j.natAdd k)) = _
  simp

private theorem block_bottom_left (Y : Rect) (Z : N) (i : J) (j : Fin k) :
    (block k q Y Z).val (i.natAdd k) (j.castAdd (q + 1)) = 0 := by
  change Matrix.fromBlocks 1 Y 0 Z.val.val
    ((blockIndices).symm (i.natAdd k)) ((blockIndices).symm (j.castAdd (q + 1))) = _
  simp

private theorem block_bottom_right (Y : Rect) (Z : N) (i j : J) :
    (block k q Y Z).val (i.natAdd k) (j.natAdd k) = Z.val.val i j := by
  change Matrix.fromBlocks 1 Y 0 Z.val.val
    ((blockIndices).symm (i.natAdd k)) ((blockIndices).symm (j.natAdd k)) = _
  simp

/-- The upper unipotent with the given rectangle and tail unipotent blocks. -/
def packedTail (Y : Rect) (Z : N) : U :=
  ⟨block k q Y Z, by
    constructor
    · intro i j
      refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
        refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j <;> intro hij
      · rw [block_top_left]
        exact Matrix.one_apply_ne (by
          have h : j₀.val < i₀.val := hij
          exact Fin.ne_of_gt h)
      · have h : k + j₁.val < i₀.val := hij
        omega
      · exact block_bottom_left k q Y Z _ _
      · rw [block_bottom_right]
        apply entry_eq_zero
        change j₁.val < i₁.val
        have h : k + j₁.val < k + i₁.val := hij
        omega
    · intro i
      refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
      · rw [block_top_left, Matrix.one_apply_eq]
      · rw [block_bottom_right, entry_diag]⟩

@[simp] theorem packedTail_top_left (Y : Rect) (Z : N) (i j : Fin k) :
    (packedTail k q Y Z).val.val (i.castAdd (q + 1)) (j.castAdd (q + 1)) =
      (1 : Matrix (Fin k) (Fin k) ℂ) i j := block_top_left k q Y Z i j

@[simp] theorem packedTail_top_right (Y : Rect) (Z : N) (i : Fin k) (j : J) :
    (packedTail k q Y Z).val.val (i.castAdd (q + 1)) (j.natAdd k) = Y i j :=
  block_top_right k q Y Z i j

@[simp] theorem packedTail_bottom_left (Y : Rect) (Z : N) (i : J) (j : Fin k) :
    (packedTail k q Y Z).val.val (i.natAdd k) (j.castAdd (q + 1)) = 0 :=
  block_bottom_left k q Y Z i j

@[simp] theorem packedTail_bottom_right (Y : Rect) (Z : N) (i j : J) :
    (packedTail k q Y Z).val.val (i.natAdd k) (j.natAdd k) = Z.val.val i j :=
  block_bottom_right k q Y Z i j

/-- In the consecutive blocks multiplication adds the second rectangle to the first times the second tail. -/
theorem packedTail_mul (X Y : Rect) (Z T : N) :
    packedTail k q X Z * packedTail k q Y T = packedTail k q (Y + X * T.val.val) (Z * T) := by
  apply Subtype.ext
  apply Units.ext
  let e := Matrix.reindexRingEquiv ℂ (finSumFinEquiv : Fin k ⊕ J ≃ I)
  change e (Matrix.fromBlocks 1 X 0 Z.val.val) * e (Matrix.fromBlocks 1 Y 0 T.val.val) =
    e (Matrix.fromBlocks 1 (Y + X * T.val.val) 0 (Z.val.val * T.val.val))
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp

/-- Left-block conjugation acts on the rectangle by left multiplication. -/
theorem packedTail_conj (g : H) (Y : Rect) (Z : N) :
    rankInclusion (q + 1) g * (packedTail k q Y Z).val * (rankInclusion (q + 1) g)⁻¹ =
      (packedTail k q (g.val * Y) Z).val := by
  apply Units.ext
  let e := Matrix.reindexRingEquiv ℂ (finSumFinEquiv : Fin k ⊕ J ≃ I)
  change e (Matrix.fromBlocks g.val 0 0 (1 : Matrix J J ℂ)) *
      e (Matrix.fromBlocks 1 Y 0 Z.val.val) * e (Matrix.fromBlocks g⁻¹.val 0 0 (1 : Matrix J J ℂ)) =
    e (Matrix.fromBlocks 1 (g.val * Y) 0 Z.val.val)
  simp only [← map_mul, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Units.mul_inv]

/-- Place a column in the first slot of the off-diagonal block. -/
def firstRectangle (x : Head) : Rect := fun i => Fin.cons (x i) 0

/-- Place a rectangle in the later slots of the off-diagonal block. -/
def laterRectangle (X : Tail) : Rect := fun i => Fin.cons 0 (X i)

private theorem firstRectangle_mul (x : Head) (Z : N) :
    firstRectangle k q x * Z.val.val = fun i => Fin.cons (x i) (firstRowCorrection k q x Z i) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [firstRectangle, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [entry_diag, mul_one, Fin.cons_zero]
  · rfl

/-- Moving the first column left gives the correction used by the rectangle measure change. -/
theorem packedTail_split (Y : Rect) (Z : N) :
    packedTail k q Y Z = packedTail k q (firstRectangle k q (fun i => Y i 0)) 1 *
      packedTail k q (laterRectangle k q (fun i j =>
        Y i j.succ - firstRowCorrection k q (fun l => Y l 0) Z i j)) Z := by
  rw [packedTail_mul, one_mul, firstRectangle_mul]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [laterRectangle]
  · simp [laterRectangle]

private theorem lead_adjacent_zero (Y : Rect) (Z : N) (hY : ∀ i, Y i 0 = 0) (i : Fin k) :
    (packedTail k q Y Z).val.val (i.castAdd q).castSucc (i.castAdd q).succ = 0 := by
  have hRow : (i.castAdd q).castSucc = i.castAdd (q + 1) := rfl
  rw [hRow]
  by_cases hi : i.val + 1 < k
  · let j : Fin k := ⟨i.val + 1, hi⟩
    have hCol : (i.castAdd q).succ = j.castAdd (q + 1) := rfl
    rw [hCol, packedTail_top_left]
    exact Matrix.one_apply_ne (fun he => by
      have h := congrArg Fin.val he
      change i.val = i.val + 1 at h
      omega)
  · have hCol : (i.castAdd q).succ = (0 : J).natAdd k := by
      apply Fin.ext
      change i.val + 1 = k + 0
      omega
    rw [hCol, packedTail_top_right, hY]

private theorem tail_adjacent_entry (Y : Rect) (Z : N) (j : Fin q) :
    (packedTail k q Y Z).val.val (j.natAdd k).castSucc (j.natAdd k).succ = Z.val.val j.castSucc j.succ := by
  have hRow : (j.natAdd k).castSucc = j.castSucc.natAdd k := rfl
  have hCol : (j.natAdd k).succ = j.succ.natAdd k := by
    apply Fin.ext
    change k + j.val + 1 = k + (j.val + 1)
    omega
  rw [hRow, hCol, packedTail_bottom_right]

/-- An upper rectangle starting at the second tail column does not add a simple-root entry. -/
theorem packedTail_adjacent_sum (Y : Rect) (Z : N) (hY : ∀ i, Y i 0 = 0) :
    (∑ i : Fin (k + q), (packedTail k q Y Z).val.val i.castSucc i.succ) =
      ∑ j : Fin q, Z.val.val j.castSucc j.succ := by
  rw [Fin.sum_univ_add (a := k) (b := q)]
  simp only [lead_adjacent_zero k q Y Z hY, tail_adjacent_entry k q Y Z, Finset.sum_const_zero, zero_add]

/-- The later columns of the off-diagonal block are the physical columns in the triangular exchange. -/
theorem packedTail_laterColumn (X : Tail) (Z : N) (j : Fin q) :
    (fun i : I => (packedTail k q (laterRectangle k q X) Z).val.val i (j.succ.natAdd k)) =
      directColumn k q X Z j := by
  funext i
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [packedTail_top_right, directColumn, dite_eq_left (show (i₀.castAdd (q + 1)).val < k from i₀.isLt)]
    rfl
  · have hk : ¬ (i₁.natAdd k).val < k := by change ¬ k + i₁.val < k; omega
    rw [packedTail_bottom_right, directColumn, dite_eq_right hk]
    exact congrArg (fun i => Z.val.val i j.succ) (Fin.ext (by change i₁.val = k + i₁.val - k; omega))

/-- The columns with preceding pivots on the Fourier side come from the transpose of the tail block. -/
theorem packedTail_transposeColumn (Z : N) (j : Fin q) :
    (fun i : I => (packedTail k q 0 Z).val.val.transpose i (j.castSucc.natAdd k)) =
      transposeColumn k q Z j := by
  funext i
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [Matrix.transpose_apply, packedTail_bottom_left, transposeColumn,
      ite_eq_left (show (i₀.castAdd (q + 1)).val < k from i₀.isLt)]
  · have hk : ¬ (i₁.natAdd k).val < k := by change ¬ k + i₁.val < k; omega
    rw [Matrix.transpose_apply, packedTail_bottom_right, transposeColumn, ite_eq_right hk]
    exact congrArg (Z.val.val j.castSucc) (Fin.ext (by change i₁.val = k + i₁.val - k; omega))

/-- The split block factors and the ordinary and Fourier column evaluations used in (10.5). -/
def ComplexGapUpperTailStatement : Prop :=
  (∀ (Y : Rect) (Z : N),
    packedTail k q Y Z = packedTail k q (firstRectangle k q (fun i => Y i 0)) 1 *
      packedTail k q (laterRectangle k q (fun i j =>
        Y i j.succ - firstRowCorrection k q (fun l => Y l 0) Z i j)) Z) ∧
  (∀ (X : Tail) (Z : N),
    (∑ i : Fin (k + q), (packedTail k q (laterRectangle k q X) Z).val.val i.castSucc i.succ) =
      ∑ j : Fin q, Z.val.val j.castSucc j.succ) ∧
  (∀ (X : Tail) (Z : N) (j : Fin q),
    (fun i : I => (packedTail k q (laterRectangle k q X) Z).val.val i (j.succ.natAdd k)) =
      directColumn k q X Z j) ∧
  (∀ (Z : N) (j : Fin q),
    (fun i : I => (packedTail k q 0 Z).val.val.transpose i (j.castSucc.natAdd k)) =
      transposeColumn k q Z j)

theorem complexGapUpperTail : ComplexGapUpperTailStatement k q :=
  ⟨packedTail_split k q, fun X Z => packedTail_adjacent_sum k q (laterRectangle k q X) Z (fun _ => rfl),
    packedTail_laterColumn k q, packedTail_transposeColumn k q⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGapUpperTail
