import Langlands.GroupScheme.MatrixRepresentationDifferential

/-! # Conjugation covariance of actual algebraic coefficient differentials -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinear.DualNumber

variable {n : Type v} [Fintype n]
variable {S : Type u} [CommRing S]

/-- Constant matrix coefficients multiply epsilon coefficients on the left. -/
theorem constantMatrix_mul_epsilonMatrix (A X : Matrix n n S) :
    A.map (TrivSqZeroExt.inlHom S S) * epsilonMatrix X =
      epsilonMatrix (A * X) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.map_apply, epsilonMatrix_apply,
    TrivSqZeroExt.inlHom_apply, TrivSqZeroExt.inl_mul_inr, smul_eq_mul,
    TrivSqZeroExt.inr_sum]

/-- Constant matrix coefficients multiply epsilon coefficients on the right. -/
theorem epsilonMatrix_mul_constantMatrix (X A : Matrix n n S) :
    epsilonMatrix X * A.map (TrivSqZeroExt.inlHom S S) =
      epsilonMatrix (X * A) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.map_apply, epsilonMatrix_apply,
    TrivSqZeroExt.inlHom_apply, TrivSqZeroExt.inr_mul_inl,
    op_smul_eq_mul, TrivSqZeroExt.inr_sum]

variable [DecidableEq n]

/-- Conjugation by an actual constant invertible matrix preserves `I + εX`. -/
theorem matrixUnit_conjugate (g : GL n S) (X : Matrix n n S) :
    matrixUnit ((g : Matrix n n S) * X * ((g⁻¹ : GL n S) : Matrix n n S)) =
      Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom S S) g *
        matrixUnit X *
        (Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom S S) g)⁻¹ := by
  apply Units.ext
  change 1 + epsilonMatrix _ =
    ((g : Matrix n n S).map (TrivSqZeroExt.inlHom S S) *
      (1 + epsilonMatrix X)) *
        (((g⁻¹ : GL n S) : Matrix n n S).map (TrivSqZeroExt.inlHom S S))
  rw [mul_add, mul_one, add_mul, constantMatrix_mul_epsilonMatrix,
    epsilonMatrix_mul_constantMatrix, ← Matrix.map_mul, g.mul_inv, Matrix.map_one]
    <;> simp

end Langlands.GroupScheme.GeneralLinear.DualNumber

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear GeneralLinear.DualNumber

variable {R : CommRingCat.{u}}
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Evaluate an actual scheme representation in invertible matrix coordinates. -/
def matrixPointsHom (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] : GL n S →* GL m S :=
  (ρ.affineMatrix (CommAlgCat.of R S)).comp
    (affinePointsEquiv n R (CommAlgCat.of R S)).symm.toMonoidHom

@[simp]
theorem matrixPointsHom_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (g : GL n S) :
    ρ.matrixPointsHom S g =
      ρ.affineMatrix (CommAlgCat.of R S)
        ((affinePointsEquiv n R (CommAlgCat.of R S)).symm g) := rfl

/-- The evaluated matrix homomorphism commutes with every test-algebra map. -/
theorem matrixPointsHom_naturality (ρ : MatrixRepresentation (groupScheme n R) m)
    (f : S →ₐ[R] T) (g : GL n S) :
    ρ.matrixPointsHom T (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      Matrix.GeneralLinearGroup.map f.toRingHom (ρ.matrixPointsHom S g) := by
  have hp :
      (affinePointsEquiv n R (CommAlgCat.of R T)).symm
          (Matrix.GeneralLinearGroup.map f.toRingHom g) =
        affineMap f ((affinePointsEquiv n R (CommAlgCat.of R S)).symm g) := by
    apply (affinePointsEquiv n R (CommAlgCat.of R T)).injective
    rw [MulEquiv.apply_symm_apply, affineMap_matrix, MulEquiv.apply_symm_apply]
  rw [matrixPointsHom_apply, hp]
  exact ρ.affineMatrix_naturality (CommAlgCat.ofHom f) _

/-- The existing differential is the first-order part of the evaluated homomorphism. -/
theorem matrixPointsHom_matrixUnit (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    ρ.matrixPointsHom (DualNumber S) (matrixUnit X) =
      matrixUnit (ρ.differential S X) :=
  ρ.differential_affineMatrix X

/-- The constructed differential intertwines actual matrix conjugation. -/
theorem differential_conjugate (ρ : MatrixRepresentation (groupScheme n R) m)
    (g : GL n S) (X : Matrix n n S) :
    ρ.differential S
        ((g : Matrix n n S) * X * ((g⁻¹ : GL n S) : Matrix n n S)) =
      (ρ.matrixPointsHom S g : Matrix m m S) * ρ.differential S X *
        (((ρ.matrixPointsHom S g)⁻¹ : GL m S) : Matrix m m S) := by
  have hinl : (TrivSqZeroExt.inlAlgHom R S S).toRingHom =
      TrivSqZeroExt.inlHom S S := by
    ext s <;> rfl
  have hc := ρ.matrixPointsHom_naturality (TrivSqZeroExt.inlAlgHom R S S) g
  rw [hinl] at hc
  have h := congrArg (ρ.matrixPointsHom (DualNumber S)) (matrixUnit_conjugate g X)
  rw [matrixPointsHom_matrixUnit,
    map_mul (ρ.matrixPointsHom (DualNumber S)),
    map_mul (ρ.matrixPointsHom (DualNumber S)),
    map_inv (ρ.matrixPointsHom (DualNumber S)),
    matrixPointsHom_matrixUnit, hc,
    ← matrixUnit_conjugate] at h
  simpa only [coefficients_matrixUnit] using congrArg coefficients h

end Langlands.GroupScheme.MatrixRepresentation
