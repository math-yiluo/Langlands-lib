import Langlands.GroupScheme.Lie.Adjoint
import Langlands.GroupScheme.MatrixRepresentationDifferentialConjugation

/-! # Linear coordinates and the adjoint action for GL_n -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear.DualNumber

variable {n : Type} [Fintype n] [DecidableEq n]
variable {R : CommRingCat.{u}}
variable {A : Type u} [CommRing A] [Algebra R A]

/-- The published actual-point kernel coordinates, bundled as a linear equivalence. -/
def pointKernelLinearEquiv : Matrix n n A ≃ₗ[A]
    Additive (lieKernel (groupScheme n R) A) where
  toEquiv := pointKernelEquiv.trans Additive.ofMul
  map_add' X Y := congrArg Additive.ofMul (pointKernelEquiv_add X Y)
  map_smul' c X := by
    apply Additive.toMul.injective
    exact (pointKernelEquiv_scale (R := R) c X).symm

@[simp] theorem pointKernelLinearEquiv_toMul (X : Matrix n n A) :
    (pointKernelLinearEquiv (R := R) X).toMul = pointKernelEquiv X := rfl

@[simp] theorem pointKernelLinearEquiv_symm (x : Additive (lieKernel (groupScheme n R) A)) :
    pointKernelLinearEquiv.symm x = pointKernelEquiv.symm x.toMul := rfl

variable {B : Type u} [CommRing B] [Algebra R B]

/-- Linear coordinates commute with actual coefficient change. -/
theorem pointKernelLinearEquiv_naturality (f : A →ₐ[R] B) (X : Matrix n n A) :
    lieKernelMapLinear (groupScheme n R) f (pointKernelLinearEquiv X) =
      pointKernelLinearEquiv (X.map f) :=
  congrArg Additive.ofMul (pointKernelEquiv_naturality f X)

/-- Conjugating `I + εX` by a constant matrix gives `I + ε(gXg⁻¹)`. -/
theorem matrixUnit_conjugation (g : GL n A) (X : Matrix n n A) :
    Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom A A) g * matrixUnit X *
        (Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom A A) g)⁻¹ =
      matrixUnit ((g : Matrix n n A) * X * ((g⁻¹ : GL n A) : Matrix n n A)) :=
  (matrixUnit_conjugate g X).symm

/-- Actual constant-point conjugation has the expected matrix formula. -/
theorem pointUnit_conjugation (g : AffinePoints n R A) (X : Matrix n n A) :
    Lie.constant (groupScheme n R) g * pointUnit X *
        (Lie.constant (groupScheme n R) g)⁻¹ =
      pointUnit ((affinePointsEquiv n R (CommAlgCat.of R A) g : Matrix n n A) * X *
        (((affinePointsEquiv n R (CommAlgCat.of R A) g)⁻¹ : GL n A) : Matrix n n A)) := by
  apply (affinePointsEquiv n R (CommAlgCat.of R (DualNumber A))).injective
  simp only [map_mul, map_inv]
  have hc : affinePointsEquiv n R (CommAlgCat.of R (DualNumber A))
      (Lie.constant (groupScheme n R) g) =
      Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom A A)
        (affinePointsEquiv n R (CommAlgCat.of R A) g) :=
    affineMap_matrix (TrivSqZeroExt.inlAlgHom R A A) g
  rw [hc, pointUnit_matrix (R := R), pointUnit_matrix (R := R)]
  exact matrixUnit_conjugation _ X

/-- The actual adjoint action is matrix conjugation in the published coordinates. -/
theorem adjoint_pointKernelLinearEquiv (g : AffinePoints n R A) (X : Matrix n n A) :
    adjoint (groupScheme n R) A g (pointKernelLinearEquiv X) =
      pointKernelLinearEquiv
        ((affinePointsEquiv n R (CommAlgCat.of R A) g : Matrix n n A) * X *
          (((affinePointsEquiv n R (CommAlgCat.of R A) g)⁻¹ : GL n A) : Matrix n n A)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact pointUnit_conjugation g X

end Langlands.GroupScheme.GeneralLinear.DualNumber
