import Langlands.Group.GL.Basic
import Mathlib.Data.Matrix.Block

/-! Upper block-unipotent matrices over a commutative ring. -/

noncomputable section

namespace Langlands.GeneralLinear

section BlockUnipotent

variable {R : Type*} [CommRing R] {a b n : ℕ}

/-- The block upper unipotent matrix `[[1, X], [0, 1]]` in block coordinates
`Fin a ⊕ Fin b`, with the actual inverse `[[1, -X], [0, 1]]`. -/
def sumBlockUnipotent (X : Matrix (Fin a) (Fin b) R) :
    Matrix.GeneralLinearGroup (Fin a ⊕ Fin b) R where
  val := Matrix.fromBlocks 1 X 0 1
  inv := Matrix.fromBlocks 1 (-X) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/-- The block upper unipotent matrix `[[1, X], [0, 1]]` in `GL_n`, for `a + b = n`, using the
standard consecutive numbering `Fin a ⊕ Fin b ≃ Fin n`. -/
def blockUnipotent (h : a + b = n) (X : Matrix (Fin a) (Fin b) R) : GeneralLinear n R :=
  reindex (finSumFinEquiv.trans (finCongr h)) (sumBlockUnipotent X)

theorem blockUnipotent_val (h : a + b = n) (X : Matrix (Fin a) (Fin b) R) :
    (blockUnipotent h X : Matrix (Fin n) (Fin n) R) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks 1 X 0 1) := rfl

@[simp]
theorem blockUnipotent_zero (h : a + b = n) :
    blockUnipotent h (0 : Matrix (Fin a) (Fin b) R) = 1 := by
  apply Units.ext
  rw [blockUnipotent_val, Matrix.fromBlocks_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv, Units.val_one]

theorem blockUnipotent_add (h : a + b = n) (X Y : Matrix (Fin a) (Fin b) R) :
    blockUnipotent h (X + Y) = blockUnipotent h X * blockUnipotent h Y := by
  apply Units.ext
  simp only [Units.val_mul, blockUnipotent_val, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem map_blockUnipotent {S : Type*} [CommRing S] (φ : R →+* S) (h : a + b = n)
    (X : Matrix (Fin a) (Fin b) R) :
    Matrix.GeneralLinearGroup.map φ (blockUnipotent h X) = blockUnipotent h (X.map φ) := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, blockUnipotent_val, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr h)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr h)).symm j with j | j <;>
    simp [Matrix.one_apply, apply_ite φ]

theorem continuous_blockUnipotent [TopologicalSpace R] [IsTopologicalRing R]
    (h : a + b = n) :
    Continuous (blockUnipotent (R := R) h) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun X : Matrix (Fin a) (Fin b) R =>
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks 1 X 0 1)
    exact (continuous_const.matrix_fromBlocks continuous_id continuous_const
      continuous_const).matrix_reindex _ _
  · change Continuous fun X : Matrix (Fin a) (Fin b) R =>
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks 1 (-X) 0 1)
    exact (continuous_const.matrix_fromBlocks continuous_neg continuous_const
      continuous_const).matrix_reindex _ _

end BlockUnipotent

end Langlands.GeneralLinear

