import Mathlib

/-!
# Block matrices of shape `(1, m)`

For a square matrix of size `m + 1` we use its head entry, the tail of its first
row, the tail of its first column and its lower-right `m × m` block.  This file
records how these blocks behave under multiplication, the determinant of a matrix
whose first-column tail vanishes, and a few explicit invertible block matrices.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix
open scoped BigOperators

variable {R : Type*} {m : ℕ}

/-- The block matrix `[[a, r], [c, D]]` with blocks of sizes `1` and `m`. -/
def blk (a : R) (r c : Fin m → R) (D : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons a r) (fun i => Fin.cons (c i) (D i)))

section blk

variable (a : R) (r c : Fin m → R) (D : Matrix (Fin m) (Fin m) R)

@[simp] theorem blk_zero_zero : blk a r c D 0 0 = a := rfl
@[simp] theorem blk_zero_succ (j : Fin m) : blk a r c D 0 j.succ = r j := rfl
@[simp] theorem blk_succ_zero (i : Fin m) : blk a r c D i.succ 0 = c i := rfl
@[simp] theorem blk_succ_succ (i j : Fin m) : blk a r c D i.succ j.succ = D i j := rfl

end blk

/-- The tail of the first row. -/
def rowT (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : Fin m → R := fun j => X 0 j.succ

/-- The tail of the first column. -/
def colT (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : Fin m → R := fun i => X i.succ 0

/-- The lower-right `m × m` block. -/
def low (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : Matrix (Fin m) (Fin m) R :=
  X.submatrix Fin.succ Fin.succ

@[simp] theorem rowT_apply (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (j : Fin m) :
    rowT X j = X 0 j.succ := rfl
@[simp] theorem colT_apply (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i : Fin m) :
    colT X i = X i.succ 0 := rfl
@[simp] theorem low_apply (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i j : Fin m) :
    low X i j = X i.succ j.succ := rfl

@[simp] theorem submatrix_succ_succ_blk (a : R) (r c : Fin m → R)
    (D : Matrix (Fin m) (Fin m) R) : (blk a r c D).submatrix Fin.succ Fin.succ = D := rfl

@[simp] theorem rowT_blk (a : R) (r c : Fin m → R) (D : Matrix (Fin m) (Fin m) R) :
    rowT (blk a r c D) = r := rfl
@[simp] theorem colT_blk (a : R) (r c : Fin m → R) (D : Matrix (Fin m) (Fin m) R) :
    colT (blk a r c D) = c := rfl
@[simp] theorem low_blk (a : R) (r c : Fin m → R) (D : Matrix (Fin m) (Fin m) R) :
    low (blk a r c D) = D := rfl

theorem blk_eta (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blk (X 0 0) (rowT X) (colT X) (low X) = X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem blk_ext {X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R} (h0 : X 0 0 = Y 0 0)
    (hr : rowT X = rowT Y) (hc : colT X = colT Y) (hD : low X = low Y) : X = Y := by
  rw [← blk_eta X, ← blk_eta Y, h0, hr, hc, hD]

section CommRing

variable [CommRing R]

theorem mul_zero_zero (X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (X * Y) 0 0 = X 0 0 * Y 0 0 + rowT X ⬝ᵥ colT Y := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, dotProduct]

theorem rowT_mul (X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    rowT (X * Y) = X 0 0 • rowT Y + rowT X ᵥ* low Y := by
  ext j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct]

theorem colT_mul (X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    colT (X * Y) = Y 0 0 • colT X + low X *ᵥ colT Y := by
  ext i
  simp [Matrix.mul_apply, Fin.sum_univ_succ, mulVec, dotProduct, mul_comm]

theorem low_mul (X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    low (X * Y) = vecMulVec (colT X) (rowT Y) + low X * low Y := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, vecMulVec_apply]

theorem blk_mul (a a' : R) (r c r' c' : Fin m → R) (D D' : Matrix (Fin m) (Fin m) R) :
    blk a r c D * blk a' r' c' D' =
      blk (a * a' + r ⬝ᵥ c') (a • r' + r ᵥ* D') (a' • c + D *ᵥ c')
        (vecMulVec c r' + D * D') := by
  apply blk_ext
  · rw [mul_zero_zero]; simp
  · rw [rowT_mul]; simp
  · rw [colT_mul]; simp
  · rw [low_mul]; simp

/-- A matrix whose first-column tail vanishes has determinant `X 0 0 * det (low X)`. -/
theorem det_of_colT_eq_zero (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (h : colT X = 0) :
    X.det = X 0 0 * (low X).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hrest : ∑ i : Fin m, (-1 : R) ^ ((i.succ : Fin (m + 1)) : ℕ) * X i.succ 0 *
      (X.submatrix (i.succ).succAbove Fin.succ).det = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have : X i.succ 0 = 0 := congrFun h i
    rw [this, mul_zero, zero_mul]
  rw [hrest, add_zero]
  simp [low, Fin.succAbove_zero]

theorem det_blk_zero (a : R) (r : Fin m → R) (D : Matrix (Fin m) (Fin m) R) :
    (blk a r 0 D).det = a * D.det :=
  det_of_colT_eq_zero _ rfl

theorem blk_one : blk (1 : R) 0 0 (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
  · simp [Matrix.one_apply_ne (Fin.succ_ne_zero i)]
  · simp [Matrix.one_apply, Fin.succ_inj]

/-! ### Explicit invertible block matrices -/

/-- The block diagonal invertible matrix `diag(α, h)`. -/
def blockDiag (α : Rˣ) (h : GL (Fin m) R) : GL (Fin (m + 1)) R where
  val := blk (α : R) 0 0 (h : Matrix (Fin m) (Fin m) R)
  inv := blk ((α⁻¹ : Rˣ) : R) 0 0 ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)
  val_inv := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> simp
  inv_val := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> simp

@[simp] theorem blockDiag_val (α : Rˣ) (h : GL (Fin m) R) :
    (blockDiag α h : Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      blk (α : R) 0 0 (h : Matrix (Fin m) (Fin m) R) := rfl

theorem blockDiag_mul (α β : Rˣ) (h k : GL (Fin m) R) :
    blockDiag α h * blockDiag β k = blockDiag (α * β) (h * k) := by
  apply Units.ext
  simp only [Units.val_mul, blockDiag_val, blk_mul]
  congr 1 <;> simp

/-- The lower unipotent matrix `[[1, 0], [y, 1]]`. -/
def lowerUnip (y : Fin m → R) : GL (Fin (m + 1)) R where
  val := blk 1 0 y 1
  inv := blk 1 0 (-y) 1
  val_inv := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> simp
  inv_val := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> simp

@[simp] theorem lowerUnip_val (y : Fin m → R) :
    (lowerUnip y : Matrix (Fin (m + 1)) (Fin (m + 1)) R) = blk 1 0 y 1 := rfl

theorem lowerUnip_add (y y' : Fin m → R) :
    lowerUnip y * lowerUnip y' = lowerUnip (y + y') := by
  apply Units.ext
  simp only [Units.val_mul, lowerUnip_val, blk_mul]
  congr 1
  · simp
  · ext j; simp
  · ext i; simp
  · simp

@[simp] theorem lowerUnip_zero : lowerUnip (0 : Fin m → R) = 1 := by
  apply Units.ext
  rw [lowerUnip_val, Units.val_one, blk_one]

theorem lowerUnip_inv (y : Fin m → R) : (lowerUnip y)⁻¹ = lowerUnip (-y) := by
  rw [inv_eq_iff_mul_eq_one, lowerUnip_add, add_neg_cancel, lowerUnip_zero]

theorem det_lowerUnip (y : Fin m → R) :
    (lowerUnip y : Matrix (Fin (m + 1)) (Fin (m + 1)) R).det = 1 := by
  rw [lowerUnip_val, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove_zero, submatrix_succ_succ_blk]

end CommRing

end Langlands.Conductor.SphericalCyclicity
