import Langlands.GroupScheme.FiniteAlgebraRightRegular
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Affine coordinates for the inverse-right-regular representation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  {d : ℕ} (b : Module.Basis (Fin d) k A)

/-- The matrix of right multiplication acts on the coefficient vector by
right multiplication in the algebra. -/
theorem rightMulMatrix_mulVec_repr (R : Type u) [CommRing R] [Algebra k R]
    (x y : R ⊗[k] A) :
    rightMulMatrix b R x *ᵥ (b.baseChange R).repr y =
      (b.baseChange R).repr (y * x) :=
  LinearMap.toMatrix_mulVec_repr (b.baseChange R) (b.baseChange R)
    (LinearMap.mulRight R x) y

/-- The all-test representation recovers its original scalar-algebra action
on every affine coefficient algebra. -/
theorem affineMatrix_rightRegularRepresentation
    (R : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme b).X) :
    (rightRegularRepresentation b).affineMatrix R x =
      rightRegularUnits b R (affinePointsEquiv b R x) := by
  let f := (Corepresented.affineSectionsIso R).inv.hom
  have hf : Function.Injective f :=
    (ConcreteCategory.bijective_of_isIso (Corepresented.affineSectionsIso R).inv).1
  have hp := Corepresented.pointsEquiv_eq_affinePointsEquiv
    (functor k A) (corepresentableBy b) R x
  change pointsEquiv b _ x =
    Units.map (Algebra.TensorProduct.map f (AlgHom.id k A)).toMonoidHom
      (affinePointsEquiv b R x) at hp
  have h := pointsEquiv_rightRegularRepresentation b x
  rw [GeneralLinear.pointsEquiv_eq_affinePointsEquiv R, hp,
    rightRegularUnits_map] at h
  apply Units.ext
  ext i j
  exact hf (congrArg (fun M => (M : Matrix.GeneralLinearGroup (Fin d) _) i j) h)

/-- Affine matrix coordinates act on the actual scalar-extended algebra
by the inverse-right-regular formula. -/
theorem affineMatrix_rightRegular_mulVec_repr
    (R : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme b).X)
    (y : R ⊗[k] A) :
    ((rightRegularRepresentation b).affineMatrix R x :
        Matrix (Fin d) (Fin d) R) *ᵥ (b.baseChange R).repr y =
      (b.baseChange R).repr (y * (affinePointsEquiv b R x)⁻¹) := by
  rw [affineMatrix_rightRegularRepresentation]
  exact rightMulMatrix_mulVec_repr b R _ y

end Langlands.GroupScheme.FiniteAlgebraUnits
