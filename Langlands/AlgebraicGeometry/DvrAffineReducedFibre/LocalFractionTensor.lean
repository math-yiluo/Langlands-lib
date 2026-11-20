import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.VerticalGenericFibre

/-! # Fraction fields in the tensor comparison at a vertical point -/

open TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section LocalizedGenericFibre

variable (R B Q G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [Algebra R B] [CommRing Q] [IsDomain Q] [IsDiscreteValuationRing Q]
    [Algebra R Q] [Algebra B Q] [IsScalarTower R B Q] [IsLocalHom (algebraMap R Q)]
    [CommRing G] [Algebra B G]

/-- With a local injective DVR map from the base to `Q`, the base change to `Q`
of the generic localization of `B` is the fraction field of `Q`. -/
def localizedGenericFibreFractionEquiv (hinj : Function.Injective (algebraMap R Q))
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G] :
    Q ⊗[B] G ≃ₐ[Q] FractionRing Q := by
  let M := Algebra.algebraMapSubmonoid Q (nonZeroDivisors R)
  have hloc : IsLocalization M (Q ⊗[B] G) := by
    have ht := IsLocalization.tensor (S := Q) G
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
    simpa only [M, Algebra.algebraMapSubmonoid_map_map] using ht
  have hlocR : IsLocalization M (Q ⊗[R] FractionRing R) :=
    IsLocalization.tensor (FractionRing R) (nonZeroDivisors R)
  have hlocQ : IsLocalization M (FractionRing Q) :=
    IsLocalization.isLocalization_of_algEquiv M (genericFibreFractionRingEquiv R Q hinj)
  exact @IsLocalization.algEquiv Q _ M (Q ⊗[B] G) _ _ hloc (FractionRing Q) _ _ hlocQ

end LocalizedGenericFibre

section NewFractionField

variable (R S E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Field E] [Algebra R E] [Algebra S E]
    [IsFractionRing S E] [IsScalarTower R S E]
    [Algebra (FractionRing R) E] [IsScalarTower R (FractionRing R) E]

local notation "K" => FractionRing R
local notation "T" => K ⊗[R] S
local instance fractionTensorRightAlgebra : Algebra S T := Algebra.TensorProduct.rightAlgebra
local instance fractionTensorRightScalarTower : IsScalarTower R S T :=
  Algebra.TensorProduct.right_isScalarTower

private def tensorFractionFieldExtensionEquivAux (hinj : Function.Injective (algebraMap R S)) :
    T ≃ₐ[S] E := by
  have hS := isFractionRing_tensor_of_localDvrMap R S hinj
  exact (Algebra.TensorProduct.commRight R S K).symm.trans
    (IsLocalization.algEquiv (nonZeroDivisors S) (S ⊗[R] K) E)

/-- The generic fibre of an injective local DVR extension is the larger
fraction field, as an algebra over the smaller fraction field. -/
def tensorFractionFieldExtensionEquiv (hinj : Function.Injective (algebraMap R S)) :
    T ≃ₐ[K] E := by
  let e := tensorFractionFieldExtensionEquivAux R S E hinj
  have he : e.toRingHom.comp (algebraMap K T) = algebraMap K E := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    change e (algebraMap K T (algebraMap R K r)) = algebraMap K E (algebraMap R K r)
    rw [← IsScalarTower.algebraMap_apply R K T, IsScalarTower.algebraMap_apply R S T, e.commutes,
      ← IsScalarTower.algebraMap_apply R S E, ← IsScalarTower.algebraMap_apply R K E]
  exact { e.toRingEquiv with commutes' := fun r => RingHom.congr_fun he r }

@[simp]
theorem tensorFractionFieldExtensionEquiv_one_tmul (hinj : Function.Injective (algebraMap R S))
    (s : S) :
    tensorFractionFieldExtensionEquiv R S E hinj (1 ⊗ₜ[R] s) = algebraMap S E s :=
  (tensorFractionFieldExtensionEquivAux R S E hinj).commutes s

variable (L : Type*) [CommRing L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]

/-- Tensoring an algebra over the generic point with the new DVR agrees with
tensoring it over the old fraction field with the new fraction field. -/
def tensorDvrEquivTensorFractionField (hinj : Function.Injective (algebraMap R S)) :
    S ⊗[R] L ≃+* L ⊗[K] E :=
  (Algebra.TensorProduct.comm R S L).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange R K K L S).symm.toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L)
        (tensorFractionFieldExtensionEquiv R S E hinj)).toRingEquiv)

@[simp]
theorem tensorDvrEquivTensorFractionField_tmul (hinj : Function.Injective (algebraMap R S))
    (s : S) (x : L) :
    tensorDvrEquivTensorFractionField R S E L hinj (s ⊗ₜ[R] x) =
      x ⊗ₜ[K] algebraMap S E s := by
  change x ⊗ₜ[K] tensorFractionFieldExtensionEquiv R S E hinj (1 ⊗ₜ[R] s) =
    x ⊗ₜ[K] algebraMap S E s
  rw [tensorFractionFieldExtensionEquiv_one_tmul]

end NewFractionField

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
