import Langlands.Algebra.TensorNorm
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Determinant norms in product coordinates -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.Algebra

variable {R I : Type u} [CommRing R] [Fintype I] [DecidableEq I]

/-- The determinant norm of a finite product algebra is the product of its coordinates. -/
theorem norm_pi (x : I → R) : Algebra.norm R x = ∏ i, x i := by
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun R I)]
  have h : Algebra.leftMulMatrix (Pi.basisFun R I) x = Matrix.diagonal x := by
    ext i j
    simp [Algebra.leftMulMatrix_apply, Pi.single_apply, Matrix.diagonal]
  rw [h, Matrix.det_diagonal]

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra A R]

/-- A product decomposition of the coefficient-first tensor algebra computes the tensor norm. -/
theorem tensorNorm_eq_prod (e : R ⊗[A] B ≃ₐ[R] (I → R)) (x : B ⊗[A] R) :
    tensorNorm A B R x = ∏ i, e (Algebra.TensorProduct.comm A B R x) i := by
  change Algebra.norm R (Algebra.TensorProduct.comm A B R x) = _
  rw [← Algebra.norm_eq_of_algEquiv e, norm_pi]

end Langlands.Algebra
