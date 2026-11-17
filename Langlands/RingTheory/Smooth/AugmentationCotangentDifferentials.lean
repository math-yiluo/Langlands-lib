import Langlands.GroupScheme.Rational.CoordinateCotangentDualityProof
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Augmentation cotangents and pulled-back Kähler differentials -/

noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace Algebra.AugmentationCotangent

open Langlands.GroupScheme.CoordinateWeights

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra A R] [IsScalarTower R A R]

local notation "I" => RingHom.ker (algebraMap A R)
local notation "Ω" => KaehlerDifferential R A

/-- The augmentation supplied by the split algebra tower. -/
abbrev augmentation : A →ₐ[R] R := IsScalarTower.toAlgHom R A R

/-- The natural algebra action on the augmentation cotangent factors through
the augmentation. -/
theorem cotangent_smul (a : A) (x : (I).Cotangent) :
    a • x = algebraMap A R a • x := by
  have hconst : algebraMap A R (algebraMap R A (algebraMap A R a)) = algebraMap A R a :=
    (augmentation R A).commutes _
  have ha : a - algebraMap R A (algebraMap A R a) ∈ I := by
    simp only [RingHom.mem_ker, map_sub, hconst, sub_self]
  have hx := Ideal.Cotangent.smul_eq_zero_of_mem ha x
  rw [sub_smul, IsScalarTower.algebraMap_smul A] at hx
  exact sub_eq_zero.mp hx

local instance cotangentTower : IsScalarTower A R (I).Cotangent :=
  IsScalarTower.of_algebraMap_smul (fun a x => (cotangent_smul R A a x).symm)

/-- The actual augmentation class is the universal derivation at the augmentation. -/
def classDerivation : Derivation R A (I).Cotangent where
  toLinearMap := AugmentedAlgebra.classMap (augmentation R A)
  map_one_eq_zero' := by
    have h := AugmentedAlgebra.classMap_algebraMap (augmentation R A) (1 : R)
    rw [map_one] at h
    exact h
  leibniz' a b := by
    rw [cotangent_smul, cotangent_smul]
    exact AugmentedAlgebra.classMap_mul (augmentation R A) a b

/-- The canonical Kähler map from the actual augmentation quotient. -/
def toTensor : (I).Cotangent →ₗ[R] R ⊗[A] Ω :=
  (KaehlerDifferential.kerCotangentToTensor R A R).restrictScalars R

@[simp]
theorem toTensor_toCotangent (a : I) :
    toTensor R A ((I).toCotangent a) = (1 : R) ⊗ₜ[A] KaehlerDifferential.D R A a.val := rfl

/-- The inverse map is obtained by the universal property of differentials and
extension of scalars through the augmentation. -/
def fromTensor : R ⊗[A] Ω →ₗ[R] (I).Cotangent :=
  (classDerivation R A).liftKaehlerDifferential.liftBaseChange R

@[simp]
theorem fromTensor_tmul_D (r : R) (a : A) :
    fromTensor R A (r ⊗ₜ[A] KaehlerDifferential.D R A a) =
      r • AugmentedAlgebra.classMap (augmentation R A) a := by
  rw [fromTensor, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

@[simp]
theorem toTensor_classMap (a : A) :
    toTensor R A (AugmentedAlgebra.classMap (augmentation R A) a) =
      (1 : R) ⊗ₜ[A] KaehlerDifferential.D R A a := by
  change toTensor R A ((I).toCotangent (AugmentedAlgebra.project (augmentation R A) a)) = _
  rw [toTensor_toCotangent]
  change (1 : R) ⊗ₜ[A] KaehlerDifferential.D R A
    (a - algebraMap R A (algebraMap A R a)) = _
  rw [map_sub, Derivation.map_algebraMap, sub_zero]

theorem fromTensor_toTensor (x : (I).Cotangent) :
    fromTensor R A (toTensor R A x) = x := by
  obtain ⟨a, rfl⟩ := (I).toCotangent_surjective x
  rw [toTensor_toCotangent, fromTensor_tmul_D, one_smul]
  exact AugmentedAlgebra.classMap_ideal (augmentation R A) a

theorem toTensor_comp_fromTensor :
    (toTensor R A).comp (fromTensor R A) = LinearMap.id := by
  apply (LinearMap.liftBaseChangeEquiv R
    (R := A) (M := Ω) (N := R ⊗[A] Ω)).symm.injective
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change toTensor R A (fromTensor R A ((1 : R) ⊗ₜ[A] KaehlerDifferential.D R A a)) =
    (1 : R) ⊗ₜ[A] KaehlerDifferential.D R A a
  rw [fromTensor_tmul_D, one_smul, toTensor_classMap]

/-- For every split augmentation, its actual cotangent is canonically the
Kähler differential module pulled back along the augmentation. -/
def cotangentEquivTensor : (I).Cotangent ≃ₗ[R] R ⊗[A] Ω where
  toLinearMap := toTensor R A
  invFun := fromTensor R A
  left_inv := fromTensor_toTensor R A
  right_inv x := LinearMap.congr_fun (toTensor_comp_fromTensor R A) x

end Algebra.AugmentationCotangent
