import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.GenericFibreBaseChange
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.LocalFractionTensor

/-! # The fraction-field presentation of normalization over a vertical DVR -/

open TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section VerticalDvr

variable (R S Q E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [CommRing Q] [IsDomain Q] [IsDiscreteValuationRing Q]
    [Algebra R Q] [IsLocalHom (algebraMap R Q)] [Field E] [Algebra R E] [Algebra S E]
    [IsFractionRing S E] [IsScalarTower R S E]
    [Algebra (FractionRing R) E] [IsScalarTower R (FractionRing R) E]
    [Algebra (FractionRing R) (FractionRing Q)] [IsScalarTower R (FractionRing R) (FractionRing Q)]

local notation "K" => FractionRing R
local notation "L" => FractionRing Q
local notation "D" => S ⊗[R] Q
local notation "H" => D ⊗[S] FractionRing S
local notation "H₁" => S ⊗[R] (Q ⊗[R] K)
local notation "H₂" => L ⊗[K] E
local instance verticalGenericTensorAlgebra : Algebra D H₁ := tensorBaseChangeAlgebra R S Q

/-- The generic fibre after changing the base of a vertical DVR is the
tensor product of the fraction fields over the original fraction field. -/
def verticalGenericFibreRingEquiv
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q)) :
    H ≃+* H₂ :=
  (genericFibreBaseChangeEquiv R S Q hinjS).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      ((genericFibreFractionRingEquiv R Q hinjQ).restrictScalars R)).toRingEquiv.trans
      (tensorDvrEquivTensorFractionField R S E L hinjS))

theorem verticalGenericFibreRingEquiv_apply_tmul
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q))
    (s : S) (q : Q) :
    verticalGenericFibreRingEquiv R S Q E hinjS hinjQ (algebraMap D H (s ⊗ₜ[R] q)) =
      algebraMap Q L q ⊗ₜ[K] algebraMap S E s := by
  let g := genericFibreBaseChangeEquiv R S Q hinjS
  let f := genericFibreFractionRingEquiv R Q hinjQ
  have hg : g (algebraMap D H (s ⊗ₜ[R] q)) = s ⊗ₜ[R] (q ⊗ₜ[R] (1 : K)) :=
    g.commutes (s ⊗ₜ[R] q)
  have hf : f (q ⊗ₜ[R] (1 : K)) = algebraMap Q L q := f.commutes q
  change tensorDvrEquivTensorFractionField R S E L hinjS
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (f.restrictScalars R))
      (g (algebraMap D H (s ⊗ₜ[R] q)))) = _
  rw [hg]
  change tensorDvrEquivTensorFractionField R S E L hinjS
    (s ⊗ₜ[R] f (q ⊗ₜ[R] (1 : K))) = _
  rw [hf, tensorDvrEquivTensorFractionField_tmul]

local instance verticalTensorRightAlgebra : Algebra Q D := Algebra.TensorProduct.rightAlgebra
local instance verticalGenericRightAlgebra : Algebra Q H := Algebra.TensorProduct.leftAlgebra
local instance verticalGenericRightScalarTower : IsScalarTower Q D H := TensorProduct.isScalarTower_left
local instance verticalLeftFractionAlgebra : Algebra Q H₂ := Algebra.compHom H₂ (algebraMap Q L)
local instance verticalRightFractionAlgebra : Algebra E H₂ := Algebra.TensorProduct.rightAlgebra

private def verticalGenericFibreAlgEquiv
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q)) :
    H ≃ₐ[Q] H₂ :=
  { verticalGenericFibreRingEquiv R S Q E hinjS hinjQ with
    commutes' := fun q => by
      change verticalGenericFibreRingEquiv R S Q E hinjS hinjQ
        (algebraMap D H (1 ⊗ₜ[R] q)) = algebraMap Q L q ⊗ₜ[K] (1 : E)
      rw [verticalGenericFibreRingEquiv_apply_tmul, map_one] }

variable [Module.Finite R S]

local notation "C" => integralClosure D H

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [IsLocalHom (algebraMap R S)] [IsDomain Q] [IsDiscreteValuationRing Q]
  [IsLocalHom (algebraMap R Q)] [Algebra K L] [IsScalarTower R K L] in
private theorem integralClosure_restrictScalars_verticalDvr :
    integralClosure Q H = (integralClosure D H).restrictScalars Q := by
  have : Module.Finite Q D := Module.Finite.equiv (Algebra.TensorProduct.commRight R Q S).toLinearEquiv
  ext x
  change IsIntegral Q x ↔ IsIntegral D x
  exact ⟨IsIntegral.tower_top, isIntegral_trans (R := Q) (A := D) x⟩

/-- After a finite extension of the base, normalization in the generic fibre
of the changed vertical DVR is the integral closure of the original vertical
DVR in the tensor of the fraction fields. -/
def verticalFractionFieldNormalizationEquiv
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q)) :
    C ≃+* integralClosure Q H₂ :=
  let e := Subalgebra.equivOfEq _ _ (integralClosure_restrictScalars_verticalDvr R S Q)
  e.symm.toRingEquiv.trans
    (verticalGenericFibreAlgEquiv R S Q E hinjS hinjQ).mapIntegralClosure.toRingEquiv

theorem verticalFractionFieldNormalizationEquiv_baseMap
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q))
    (s : S) :
    (verticalFractionFieldNormalizationEquiv R S Q E hinjS hinjQ (algebraMap S C s)).val =
      algebraMap E H₂ (algebraMap S E s) := by
  change verticalGenericFibreRingEquiv R S Q E hinjS hinjQ
    (algebraMap D H (s ⊗ₜ[R] (1 : Q))) = (1 : L) ⊗ₜ[K] algebraMap S E s
  rw [verticalGenericFibreRingEquiv_apply_tmul, map_one]

end VerticalDvr

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
