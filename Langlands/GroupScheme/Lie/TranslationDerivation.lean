import Langlands.GroupScheme.Lie.ConjugationDerivation

/-! # Coordinate derivations from actual infinitesimal translation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A B : Type u} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

/-- Translate a constant point on the left by the coefficient extension
of an actual identity-kernel point. -/
def infinitesimalTranslate (X : lieKernel G R) (g : AffinePoints G A) :
    AffinePoints G (DualNumber A) :=
  (lieKernelMap G (Algebra.ofId R A) X).val * constant G g

@[simp] theorem reduction_infinitesimalTranslate
    (X : lieKernel G R) (g : AffinePoints G A) :
    reduction G (infinitesimalTranslate G X g) = g := by
  have hx : reduction G (lieKernelMap G (Algebra.ofId R A) X).val = 1 :=
    (lieKernelMap G (Algebra.ofId R A) X).property
  simp only [infinitesimalTranslate, map_mul, hx, reduction_constant, one_mul]

/-- Infinitesimal translation is natural on every affine test algebra. -/
theorem infinitesimalTranslate_naturality (f : A →ₐ[R] B)
    (X : lieKernel G R) (g : AffinePoints G A) :
    affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f)
        (infinitesimalTranslate G X g) =
      infinitesimalTranslate G X (affineMap G f g) := by
  have hf : f.comp (Algebra.ofId R A) = Algebra.ofId R B := Subsingleton.elim _ _
  have hx : affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f)
      (lieKernelMap G (Algebra.ofId R A) X).val =
      (lieKernelMap G (Algebra.ofId R B) X).val := by
    change (lieKernelMap G f (lieKernelMap G (Algebra.ofId R A) X)).val = _
    rw [← lieKernelMap_comp, hf]
  simp only [infinitesimalTranslate, map_mul, hx, constant_naturality]

@[simp] theorem infinitesimalTranslate_one (X : lieKernel G R) :
    infinitesimalTranslate G X (1 : AffinePoints G R) = X.val := by
  have hi : Algebra.ofId R R = AlgHom.id R R := Subsingleton.elim _ _
  simp only [infinitesimalTranslate, map_one, mul_one, hi, lieKernelMap_id]

variable [IsAffineHom G.X.hom]

/-- The coordinate map of infinitesimal translation of the universal point. -/
def translationLift (X : lieKernel G R) :
    coordinateAlgebra G →ₐ[R] DualNumber (coordinateAlgebra G) :=
  pointCoordinates G (infinitesimalTranslate G X (universalPoint G))

@[simp] theorem translationLift_fst (X : lieKernel G R) :
    (TrivSqZeroExt.fstHom R (coordinateAlgebra G) (coordinateAlgebra G)).comp
      (translationLift G X) = AlgHom.id R (coordinateAlgebra G) := by
  rw [translationLift, ← pointCoordinates_naturality]
  change pointCoordinates G (reduction G _) = _
  rw [reduction_infinitesimalTranslate, pointCoordinates_universalPoint]

/-- The global coordinate derivation of left infinitesimal translation. -/
def translationDerivation (X : lieKernel G R) :
    Derivation R (coordinateAlgebra G) (coordinateAlgebra G) :=
  liftDerivation (translationLift G X) (translationLift_fst G X)

@[simp] theorem translationDerivation_apply (X : lieKernel G R)
    (c : coordinateAlgebra G) :
    translationDerivation G X c = (translationLift G X c).snd := rfl

/-- The dual-number lift recovers the original translation map. -/
theorem derivationLift_translationDerivation (X : lieKernel G R) :
    derivationLift (translationDerivation G X) = translationLift G X := by
  apply AlgHom.ext
  intro c
  apply TrivSqZeroExt.ext
  · exact (DFunLike.congr_fun (translationLift_fst G X) c).symm
  · rfl

/-- Coordinates of infinitesimal translation at an arbitrary affine point. -/
theorem pointCoordinates_infinitesimalTranslate
    (X : lieKernel G R) (g : AffinePoints G A) :
    pointCoordinates G (infinitesimalTranslate G X g) =
      (GeneralLinear.DualNumber.coefficientAlgMap (pointCoordinates G g)).comp
        (derivationLift (translationDerivation G X)) := by
  rw [derivationLift_translationDerivation]
  have hn := pointCoordinates_naturality G
    (GeneralLinear.DualNumber.coefficientAlgMap (pointCoordinates G g))
    (infinitesimalTranslate G X (universalPoint G))
  rw [infinitesimalTranslate_naturality, affineMap_universalPoint,
    Equiv.symm_apply_apply] at hn
  exact hn

/-- The infinitesimal coefficient is evaluation of the global derivation. -/
theorem pointCoordinates_infinitesimalTranslate_snd
    (X : lieKernel G R) (g : AffinePoints G A) (c : coordinateAlgebra G) :
    (pointCoordinates G (infinitesimalTranslate G X g) c).snd =
      pointCoordinates G g (translationDerivation G X c) := by
  rw [pointCoordinates_infinitesimalTranslate]
  rfl

local instance identityCoordinateAlgebra : Algebra (coordinateAlgebra G) R :=
  (coordinateOrigin G).toRingHom.toAlgebra

local instance identityCoordinateScalarTower : IsScalarTower R (coordinateAlgebra G) R :=
  IsScalarTower.of_algHom (coordinateOrigin G)

/-- Evaluate a global coordinate derivation at the actual identity point. -/
def derivationAtIdentity
    (D : Derivation R (coordinateAlgebra G) (coordinateAlgebra G)) :
    IdentityDerivation G (A := R) where
  toFun c := coordinateOrigin G (D c)
  map_add' c e := by simp
  map_smul' r c := by simp
  map_one_eq_zero' := by simp
  leibniz' c e := by
    change coordinateOrigin G (D (c * e)) =
      coordinateOrigin G c * coordinateOrigin G (D e) +
        coordinateOrigin G e * coordinateOrigin G (D c)
    simp [Derivation.leibniz, smul_eq_mul]

@[simp] theorem derivationAtIdentity_apply
    (D : Derivation R (coordinateAlgebra G) (coordinateAlgebra G))
    (c : coordinateAlgebra G) :
    derivationAtIdentity G D c = coordinateOrigin G (D c) := rfl

/-- The actual identity-kernel point of an evaluated global derivation. -/
def kernelOfDerivation
    (D : Derivation R (coordinateAlgebra G) (coordinateAlgebra G)) :
    lieKernel G R :=
  (kernelDerivationEquiv G).symm (derivationAtIdentity G D)

@[simp] theorem kernelDerivationEquiv_kernelOfDerivation
    (D : Derivation R (coordinateAlgebra G) (coordinateAlgebra G)) :
    kernelDerivationEquiv G (kernelOfDerivation G D) = derivationAtIdentity G D :=
  (kernelDerivationEquiv G).apply_symm_apply _

/-- The actual kernel coordinates are the identity evaluation of the derivation. -/
theorem pointCoordinates_kernelOfDerivation_snd
    (D : Derivation R (coordinateAlgebra G) (coordinateAlgebra G))
    (c : coordinateAlgebra G) :
    (pointCoordinates G (kernelOfDerivation G D).val c).snd =
      coordinateOrigin G (D c) := by
  exact DFunLike.congr_fun (kernelDerivationEquiv_kernelOfDerivation G D) c

/-- Evaluating the translation derivation at identity recovers the original
actual tangent vector. -/
@[simp] theorem kernelOfDerivation_translationDerivation (X : lieKernel G R) :
    kernelOfDerivation G (translationDerivation G X) = X := by
  apply (kernelDerivationEquiv G).injective
  rw [kernelDerivationEquiv_kernelOfDerivation]
  ext c
  have h := pointCoordinates_infinitesimalTranslate_snd G X
    (1 : AffinePoints G R) c
  rw [infinitesimalTranslate_one] at h
  exact h.symm

end Langlands.GroupScheme.Lie
