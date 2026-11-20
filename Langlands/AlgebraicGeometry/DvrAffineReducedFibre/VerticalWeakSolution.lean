import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.LocalizedFibreTest
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.RamificationIndexOne
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.VerticalFractionFieldNormalization

/-! # Reduced generic tensors and weak solutions at vertical DVRs -/

open IsLocalRing TensorProduct

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section ReducedGenericTensor

variable (R S E B G : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Field E] [Algebra R E] [Algebra S E]
    [IsFractionRing S E] [IsScalarTower R S E]
    [Algebra (FractionRing R) E] [IsScalarTower R (FractionRing R) E]
    [CommRing B] [Algebra R B] [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]
    (p : Ideal B) [p.IsPrime]

local notation "K" => FractionRing R
local notation "Q" => Localization.AtPrime p
local notation "L" => FractionRing Q
local notation "H" => S ⊗[R] G
local notation "Hₚ" => Q ⊗[B] H
local notation "Gₚ" => Q ⊗[B] G
local instance reducedGenericTensorRightAlgebra : Algebra G H := Algebra.TensorProduct.rightAlgebra
local instance reducedGenericTensorBaseAlgebra : Algebra B H := Algebra.compHom H (algebraMap B G)
local instance reducedGenericTensorLocalizedAlgebra : Algebra H Hₚ := Algebra.TensorProduct.rightAlgebra
local instance reducedGenericTensorLocalizedGenericAlgebra : Algebra R Gₚ :=
  Algebra.TensorProduct.leftAlgebra
local instance reducedGenericTensorLocalizedGenericTower : IsScalarTower R Q Gₚ :=
  TensorProduct.isScalarTower_left

set_option maxHeartbeats 800000 in
/-- At an original vertical DVR, the tensor of its fraction field with the
new fraction field is reduced if the surrounding base-changed generic
algebra is reduced. -/
theorem isReduced_fractionFieldTensor_of_reduced_genericTensor
    [IsDomain Q] [IsDiscreteValuationRing Q] [IsLocalHom (algebraMap R Q)]
    [Algebra K L] [IsScalarTower R K L]
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q))
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G)
    (hred : IsReduced H) : IsReduced (L ⊗[K] E) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid H p.primeCompl) Hₚ :=
    IsLocalization.tensorRight Q p.primeCompl
  have : IsReduced Hₚ :=
    isReduced_localizationPreserves (Algebra.algebraMapSubmonoid H p.primeCompl) Hₚ hred
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G := hloc
  let e₀ := tensorScalarExchangeEquiv R S B Q G
  let f : Gₚ ≃ₐ[Q] L := localizedGenericFibreFractionEquiv R B Q G hinjQ
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (f.restrictScalars R)
  let e₂ := tensorDvrEquivTensorFractionField R S E L hinjS
  let e := e₀.trans (e₁.toRingEquiv.trans e₂)
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end ReducedGenericTensor

section Solution

variable (R S Q E X C : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [CommRing Q] [IsDomain Q] [IsDiscreteValuationRing Q] [Algebra R Q]
    [IsLocalHom (algebraMap R Q)] [Field E] [Algebra R E] [Algebra S E]
    [IsFractionRing S E] [IsScalarTower R S E]
    [Algebra (FractionRing R) E] [IsScalarTower R (FractionRing R) E]
    [Algebra (FractionRing R) (FractionRing Q)] [IsScalarTower R (FractionRing R) (FractionRing Q)]
    [CommRing X] [Algebra Q X] [CommRing C] [Algebra Q C] [Algebra C X]
    [IsScalarTower Q C X] [IsIntegralClosure C Q X] [Algebra S C]

local notation "K" => FractionRing R
local notation "L" => FractionRing Q
local notation "D" => S ⊗[R] Q
local notation "H" => L ⊗[K] E
local notation "N" => integralClosure D (D ⊗[S] FractionRing S)
local instance verticalSolutionLeftAlgebra : Algebra Q H := Algebra.compHom H (algebraMap Q L)

set_option maxHeartbeats 800000 in
/-- A scalar-compatible presentation of the integral closure of the
vertical DVR in the tensor of fraction fields gives the same normalized
generic-fibre algebra. -/
def verticalSolutionNormalizationEquiv
    (e : X ≃ₐ[Q] H)
    (hS : ∀ s : S, e (algebraMap C X (algebraMap S C s)) = (1 : L) ⊗ₜ[K] algebraMap S E s)
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q)) :
    N ≃ₐ[S] C := by
  let f := verticalFractionFieldNormalizationEquiv R S Q E hinjS hinjQ
  let g := (IsIntegralClosure.equiv Q C X (integralClosure Q X)).trans e.mapIntegralClosure
  refine { f.trans g.symm.toRingEquiv with commutes' := fun s => ?_ }
  change g.symm (f (algebraMap S N s)) = algebraMap S C s
  apply g.injective
  rw [g.apply_symm_apply]
  apply Subtype.ext
  calc
    _ = (1 : L) ⊗ₜ[K] algebraMap S E s :=
      verticalFractionFieldNormalizationEquiv_baseMap R S Q E hinjS hinjQ s
    _ = e (algebraMap C X (algebraMap S C s)) := (hS s).symm
    _ = _ := congrArg e (IsIntegralClosure.algebraMap_equiv Q C X (integralClosure Q X) _).symm

set_option maxHeartbeats 800000 in
/-- A weak solution presented as an integral closure in the tensor of
fraction fields gives a reduced normalized residue fibre. -/
theorem isReduced_normalizedResidue_of_verticalSolution
    (e : X ≃ₐ[Q] H)
    (hS : ∀ s : S, e (algebraMap C X (algebraMap S C s)) = (1 : L) ⊗ₜ[K] algebraMap S E s)
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q))
    (hidx : ∀ (P : Ideal C), P.IsMaximal → P.ramificationIdx S = 1) :
    IsReduced (ResidueField S ⊗[S] N) := by
  have hcompat (r : R) :
      algebraMap Q C (algebraMap R Q r) = algebraMap S C (algebraMap R S r) := by
    apply (IsIntegralClosure.algebraMap_injective C Q X)
    apply e.injective
    rw [← IsScalarTower.algebraMap_apply Q C X, e.commutes, hS]
    change algebraMap Q L (algebraMap R Q r) ⊗ₜ[K] (1 : E) =
      (1 : L) ⊗ₜ[K] algebraMap S E (algebraMap R S r)
    rw [
      ← IsScalarTower.algebraMap_apply R Q L, ← IsScalarTower.algebraMap_apply R S E,
      IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K E]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := K) (algebraMap R K r)
  have : Algebra.IsIntegral Q C := IsIntegralClosure.isIntegral_algebra Q X
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hcontain (P : Ideal C) (hP : P.IsMaximal) : algebraMap S C t ∈ P := by
    have : P.IsPrime := hP.isPrime
    exact (mem_baseUniformizer_iff_isMaximal R S Q C hinjS hinjQ hcompat ht P).mpr hP
  have : IsReduced (ResidueField S ⊗[S] C) :=
    isReduced_residueTensor_of_ramificationIdx_eq_one S C ht hcontain hidx
  let f := verticalSolutionNormalizationEquiv R S Q E X C e hS hinjS hinjQ
  let g := Algebra.TensorProduct.congr
    (AlgEquiv.refl : ResidueField S ≃ₐ[ResidueField S] ResidueField S) f
  exact isReduced_of_injective g.toRingHom g.injective

end Solution

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
