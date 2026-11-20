import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.NormalizationBaseChange
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.VerticalPrimeContraction

/-! # Base change of a generic fibre along an injective local map of DVRs -/

open TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section GenericFibre

variable (R S A : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [CommRing A] [Algebra R A]

local notation "D" => S ⊗[R] A
local notation "G" => A ⊗[R] FractionRing R
local notation "H" => S ⊗[R] G
local notation "N" => integralClosure A G
local notation "Nₛ" => S ⊗[R] N

local instance : Algebra D H := tensorBaseChangeAlgebra R S A
local instance : IsScalarTower S D H := tensorBaseChangeAlgebra_isScalarTower R S A

/-- Changing the DVR and taking the generic fibre agrees with scalar extension
of the original generic fibre. The equivalence preserves the base-changed
algebra structure. -/
def genericFibreBaseChangeEquiv (hinj : Function.Injective (algebraMap R S)) :
    D ⊗[S] FractionRing S ≃ₐ[D] H := by
  let M := nonZeroDivisors R
  let M' := Algebra.algebraMapSubmonoid D M
  let Mₛ := Algebra.algebraMapSubmonoid S M
  let Mₐ := Algebra.algebraMapSubmonoid A M
  have : IsLocalization Mₛ (S ⊗[R] FractionRing R) := IsLocalization.tensor _ M
  have : IsLocalization Mₛ (FractionRing S) :=
    IsLocalization.isLocalization_of_algEquiv Mₛ (genericFibreFractionRingEquiv R S hinj)
  have hleft : IsLocalization M' (D ⊗[S] FractionRing S) := by
    have ht : IsLocalization (Algebra.algebraMapSubmonoid D Mₛ) (D ⊗[S] FractionRing S) :=
      IsLocalization.tensor _ Mₛ
    simpa only [M', Mₛ, Algebra.algebraMapSubmonoid_map_map] using ht
  have : IsLocalization Mₐ G := IsLocalization.tensor _ M
  let j : A →ₐ[R] D := Algebra.TensorProduct.includeRight
  have hright : IsLocalization (Mₐ.map j) H := by
    apply IsLocalization.tensorProduct_tensorProduct_right R S Mₐ G
    ext a
    rfl
  have hright' : IsLocalization M' H := by
    simpa only [M', Mₐ, Algebra.algebraMapSubmonoid_map_eq] using hright
  exact IsLocalization.algEquiv M' _ _

local instance : Algebra Nₛ H := tensorBaseChangeAlgebra R S N (B := G)
local instance : IsScalarTower S Nₛ H := tensorBaseChangeAlgebra_isScalarTower R S N (B := G)

/-- After changing the DVR, the normalization in the new generic fibre agrees
with the integral closure computed from the old normalization and old generic
fibre after tensoring with the new base. -/
def normalizationTensorBaseChangeEquiv (hinj : Function.Injective (algebraMap R S)) :
    integralClosure D (D ⊗[S] FractionRing S) ≃ₐ[S] integralClosure Nₛ H :=
  ((genericFibreBaseChangeEquiv R S A hinj).mapIntegralClosure.restrictScalars S).trans
    (integralClosureTensorTowerEquiv R S A N G)

end GenericFibre

section GoingDown

variable (R S B G : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing B] [Algebra R B] [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]

local notation "Bₛ" => S ⊗[R] B
local notation "Gₛ" => S ⊗[R] G
local instance : Algebra Bₛ Gₛ := tensorBaseChangeAlgebra R S B (B := G)
local notation "B'" => integralClosure Bₛ Gₛ

local instance : Algebra B Bₛ := Algebra.TensorProduct.rightAlgebra
local instance : Algebra G Gₛ := Algebra.TensorProduct.rightAlgebra
local instance : Algebra B Gₛ := Algebra.compHom Gₛ (algebraMap B G)
local instance : IsScalarTower B G Gₛ := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance : IsScalarTower B Bₛ Gₛ := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The algebra structure on the normalization after tensor base change from
the original algebra on the right. -/
@[instance_reducible]
def normalizationTensorAlgebra : Algebra B B' := inferInstance

/-- Integral closure after an integral flat base change has going down over
an original algebra with normal domain localizations, when the ambient algebra
is flat over that algebra. -/
theorem hasGoingDown_normalizationTensor [Algebra.IsIntegral R S] [Module.Flat R S]
    [Module.Flat B G] (hNormal : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    letI := normalizationTensorAlgebra R S B G
    Algebra.HasGoingDown B B' := by
  have : Algebra.IsIntegral B Bₛ := by
    constructor
    intro x
    let e := Algebra.TensorProduct.commRight R B S
    rw [← e.apply_symm_apply x]
    exact (Algebra.IsIntegral.isIntegral (e.symm x)).map e
  have : Algebra.IsIntegral B B' := ⟨fun x =>
    isIntegral_trans (R := B) (A := Bₛ) x (Algebra.IsIntegral.isIntegral x)⟩
  have : Module.Flat G Gₛ := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight R G S).symm.toLinearEquiv
  have : Module.Flat B Gₛ := Module.Flat.trans B G Gₛ
  exact hasGoingDown_of_normal_localizations_of_flat_embedding B B' Gₛ hNormal Subtype.val_injective

end GoingDown

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
