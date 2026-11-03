import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Int.Basic

/-! # Integer weight components of coordinate vectors -/

namespace Langlands.GroupScheme.GeneralLinear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

/-- The weight-`w` component of a vector for the weights `a`. -/
def weightPart (a : ι → ℤ) (w : ℤ) (c : ι → K) : ι → K :=
  fun i => if a i = w then c i else 0

omit [Fintype ι] [DecidableEq ι] in
theorem weightPart_add (a : ι → ℤ) (w : ℤ) (c c' : ι → K) :
    weightPart a w (c + c') = weightPart a w c + weightPart a w c' := by
  funext i
  simp only [weightPart, Pi.add_apply]
  split_ifs <;> simp

end Langlands.GroupScheme.GeneralLinear
