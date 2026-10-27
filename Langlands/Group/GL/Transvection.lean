import Langlands.Group.GL.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Elementary transvections as invertible matrices -/

namespace Langlands.GeneralLinear

universe uF

variable {F : Type uF} [Field F]

/-- A transvection, including its explicit inverse. -/
def transvectionUnit {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : F) :
    GeneralLinear k F where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp

end Langlands.GeneralLinear
