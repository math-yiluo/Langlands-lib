import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Lie.SmoothScalarExtension
import Mathlib.RingTheory.Derivation.ToSquareZero

/-! # Affine-group reduction kernels and derivations into square-zero ideals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Lie.SquareZero

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
variable {A : Type u} [CommRing A] [Algebra R A] (I : Ideal A)

/-- Reduction of actual affine points modulo an arbitrary ideal. -/
def reduction : AffinePoints G A →* AffinePoints G (A ⧸ I) :=
  affineMap G (Ideal.Quotient.mkₐ R I)

/-- The actual pointwise reduction kernel in an affine coefficient ring. -/
abbrev kernel := (reduction G I).ker

attribute [local instance] coordinateOriginAlgebra

/-- Actual reduction-kernel points are exactly lifts of the coordinate
augmentation through the quotient algebra. -/
def kernelCoordinates : kernel G I ≃
    {f : coordinateAlgebra G →ₐ[R] A //
      (Ideal.Quotient.mkₐ R I).comp f =
        IsScalarTower.toAlgHom R (coordinateAlgebra G) (A ⧸ I)} where
  toFun x := ⟨pointCoordinates G x.val, by
    rw [← pointCoordinates_naturality]
    change pointCoordinates G (reduction G I x.val) = _
    rw [x.property, pointCoordinates_one]
    rfl⟩
  invFun f := ⟨(pointCoordinates G).symm f.val, by
    change reduction G I _ = 1
    apply (pointCoordinates G).injective
    change pointCoordinates G (affineMap G (Ideal.Quotient.mkₐ R I) _) = _
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply, f.property,
      pointCoordinates_one]
    rfl⟩
  left_inv x := Subtype.ext ((pointCoordinates G).symm_apply_apply x.val)
  right_inv f := Subtype.ext ((pointCoordinates G).apply_symm_apply f.val)

/-- Kernel points modulo a square-zero ideal correspond to actual coordinate
derivations into that ideal, with the augmentation action on coefficients. -/
def kernelDerivationEquiv (hI : I ^ 2 = ⊥) :
    kernel G I ≃ Derivation R (coordinateAlgebra G) I :=
  (kernelCoordinates G I).trans (derivationToSquareZeroEquivLift I hI).symm

/-- The coordinate derivation is the difference from the identity section. -/
theorem kernelDerivationEquiv_apply (hI : I ^ 2 = ⊥) (x : kernel G I)
    (b : coordinateAlgebra G) :
    (kernelDerivationEquiv G I hI x b : A) =
      pointCoordinates G x.val b - algebraMap (coordinateAlgebra G) A b := rfl

variable {B : Type u} [CommRing B] [Algebra R B]

/-- Coordinate derivations of compatible actual kernel points commute with
extension of coefficients. No flatness assumption is needed for this
ideal-valued coordinate comparison. -/
theorem kernelDerivationEquiv_naturality (J : Ideal B)
    (hI : I ^ 2 = ⊥) (hJ : J ^ 2 = ⊥) (f : A →ₐ[R] B)
    (x : kernel G I) (y : kernel G J) (hxy : affineMap G f x.val = y.val)
    (b : coordinateAlgebra G) :
    (kernelDerivationEquiv G J hJ y b : B) =
      f (kernelDerivationEquiv G I hI x b) := by
  rw [kernelDerivationEquiv_apply, kernelDerivationEquiv_apply, ← hxy,
    pointCoordinates_naturality, AlgHom.comp_apply, map_sub]
  congr 1
  change algebraMap R B (coordinateOrigin G b) =
    f (algebraMap R A (coordinateOrigin G b))
  exact (f.commutes _).symm

local instance coordinateOriginBaseScalarTower :
    IsScalarTower (coordinateAlgebra G) R A :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The identity cotangent universal property with values in an arbitrary
coefficient ideal. -/
def idealCotangentHomEquiv :
    (identityCotangent G →ₗ[R] I) ≃ₗ[R] Derivation R (coordinateAlgebra G) I :=
  (LinearMap.liftBaseChangeEquiv R).symm.trans
    ((KaehlerDifferential.linearMapEquivDerivation R
      (coordinateAlgebra G)).restrictScalars R)

/-- The actual square-zero reduction kernel, as linear maps from the actual
identity cotangent module into the actual coefficient ideal. -/
def kernelCotangentEquiv (hI : I ^ 2 = ⊥) :
    kernel G I ≃ (identityCotangent G →ₗ[R] I) :=
  (kernelDerivationEquiv G I hI).trans (idealCotangentHomEquiv G I).symm.toEquiv

/-- For a smooth affine group the actual square-zero reduction kernel is in
bijection with the actual coefficient ideal tensored with the actual Lie
module. This is an equivalence of underlying sets; no group-law comparison is
claimed in this declaration. -/
def kernelTensorEquiv [Smooth G.X.hom] (hI : I ^ 2 = ⊥) :
    kernel G I ≃ I ⊗[R] Additive (lieKernel G R) :=
  (kernelCotangentEquiv G I hI).trans
    (dualTensorHomEquiv R (identityCotangent G) I).symm.toEquiv |>.trans
      (((TensorProduct.congr (kernelIdentityCotangentDualEquiv G).symm
        (LinearEquiv.refl R I)).trans (TensorProduct.comm R _ I)).toEquiv)

end Langlands.GroupScheme.Lie.SquareZero
