import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.LocalRamificationCriterion

/-! # Local tests for the affine reduced fibre over a complete base extension -/

open IsLocalRing TensorProduct

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Transport

variable {S B C : Type*} [CommRing S] [CommRing B] [CommRing C] [Algebra S B] [Algebra S C]

/-- The uniformizer criterion is invariant under an algebra equivalence over
the base. -/
theorem baseUniformizerAtGenericPoints_of_algEquiv (e : B ≃ₐ[S] C) (t : S)
    (h : BaseUniformizerAtGenericPoints S C t) : BaseUniformizerAtGenericPoints S B t := by
  intro q hqPrime hq
  let J := q.comap e.symm.toRingHom
  have hJPrime : J.IsPrime := Ideal.IsPrime.comap _
  have hSpan : (Ideal.span {algebraMap S B t}).comap e.symm.toRingHom =
      Ideal.span {algebraMap S C t} := by
    calc
      _ = (Ideal.span {algebraMap S B t}).map e.toRingHom :=
        Ideal.comap_symm e.toRingEquiv
      _ = _ := by
        rw [Ideal.map_span, Set.image_singleton]
        exact congrArg (fun a : C => Ideal.span {a}) (e.commutes t)
  have hJ : (Ideal.span {algebraMap S C t}).IsMinimalPrime J :=
    hSpan ▸ Ideal.minimalPrimes_comap_of_surjective e.symm.surjective hq
  have hqJ : q = J.comap e.toRingHom := (Ideal.comap_of_equiv e.toRingEquiv).symm
  let E := Localization.AtPrime q
  let F := Localization.AtPrime J
  let f : E ≃ₐ[S] F := Localization.localAlgEquiv q J e hqJ
  have hmap := congrArg (Ideal.map f.symm.toRingHom) (h J hJ)
  rw [Ideal.map_span, Set.image_singleton] at hmap
  refine Eq.trans ?_ (hmap.trans (IsLocalRing.map_ringEquiv_maximalIdeal f.symm.toRingEquiv))
  exact congrArg (fun a : E => Ideal.span {a}) (f.symm.commutes t).symm

end Transport

section TensorNormalization

variable (R S B G : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing B] [Algebra R B] [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]

local notation "D" => S ⊗[R] B
local notation "H" => S ⊗[R] G
local instance : Algebra D H := tensorBaseChangeAlgebra R S B (B := G)
local instance : IsScalarTower S D H := tensorBaseChangeAlgebra_isScalarTower R S B (B := G)
local notation "C" => integralClosure D H

local instance : Algebra B D := Algebra.TensorProduct.rightAlgebra
local instance : Algebra G H := Algebra.TensorProduct.rightAlgebra
local instance : Algebra B H := Algebra.compHom H (algebraMap B G)
local instance : IsScalarTower B D H := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance : Algebra B C := normalizationTensorAlgebra R S B G
local instance : IsScalarTower B D C := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The new base acts on the tensor normalization localized at an original prime,
through the global tensor normalization. -/
def localTensorNormalizationBaseMap (p : Ideal B) [p.IsPrime] :
    S →+* localTensorNormalization R S B G p :=
  (integralClosureTensorLocalizationMap B D H p.primeCompl).toRingHom.comp (algebraMap S C)

/-- A uniformizer test at each maximal localization of the tensor normalization
localized at an original prime. -/
abbrev LocalUniformizerTest (t : S) (p : Ideal B) [p.IsPrime] : Prop :=
  let E := localTensorNormalization R S B G p
  ∀ (J : Ideal E) (hJ : J.IsMaximal),
    letI : J.IsPrime := hJ.isPrime
    Ideal.span {algebraMap E (Localization.AtPrime J) (localTensorNormalizationBaseMap R S B G p t)}
      = maximalIdeal (Localization.AtPrime J)

/-- A version of the local-to-global criterion using the canonical map from
the new base to each local normalization. -/
theorem baseUniformizerAtGenericPoints_of_localUniformizerTest
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S] [Module.Flat R S] [Module.Flat B G]
    (hinj : Function.Injective (algebraMap R S)) {π : R} (hπ : Irreducible π)
    {t : S} (ht : Irreducible t)
    (hNormal : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hLocal : ∀ (p : Ideal B) [p.IsPrime], (Ideal.span {algebraMap R B π}).IsMinimalPrime p →
      LocalUniformizerTest R S B G t p) :
    BaseUniformizerAtGenericPoints S C t := by
  exact baseUniformizerAtGenericPoints_of_localTests R S B G hinj hπ ht hNormal hLocal

end TensorNormalization

section CompleteBase

variable (R S A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S] [Module.Flat R S]
    [IsAdicComplete (maximalIdeal S) S] [PerfectField (ResidueField S)]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FiniteType R A]
    [Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A)]

local notation "G" => A ⊗[R] FractionRing R
local notation "N" => integralClosure A G
local notation "Aₛ" => S ⊗[R] A
local notation "Nₛ" => integralClosure Aₛ (Aₛ ⊗[S] FractionRing S)

set_option maxHeartbeats 1000000 in
/-- A complete extension of DVRs with perfect residue field has finite
normalization and geometrically reduced fibres if its uniformizer passes the
local tests at the generic points of the original normalized special fibre. -/
theorem finite_normalization_and_reduced_fibres_of_localUniformizerTests
    (hinj : Function.Injective (algebraMap R S)) {π : R} (hπ : Irreducible π)
    {t : S} (ht : Irreducible t)
    (hLocal : ∀ (p : Ideal N) [p.IsPrime], (Ideal.span {algebraMap R N π}).IsMinimalPrime p →
      LocalUniformizerTest R S N G t p) :
    Module.Finite Aₛ Nₛ ∧ ∀ (F : Type u) [Field F] [Algebra S F], IsReduced (F ⊗[S] Nₛ) := by
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid N (nonZeroDivisors R)) G :=
    isLocalization_integralClosure_genericFibre R A
  have : Module.Flat N G := @IsLocalization.flat N G _ _ _
    (Algebra.algebraMapSubmonoid N (nonZeroDivisors R)) hloc
  have hgen := baseUniformizerAtGenericPoints_of_localUniformizerTest R S N G hinj hπ ht
    (fun p _ => normal_localizations_genericNormalization R A p) hLocal
  have hnorm : BaseUniformizerAtGenericPoints S Nₛ t :=
    baseUniformizerAtGenericPoints_of_algEquiv (normalizationTensorBaseChangeEquiv R S A hinj) t hgen
  have : Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] Aₛ) :=
    smooth_genericFibre_baseChange (A := A) hinj
  have : Algebra.FiniteType S Aₛ := Algebra.FiniteType.baseChange (R := R) (A := A) S
  exact finite_normalization_and_reduced_fibres_of_uniformizer S Aₛ ht hnorm

end CompleteBase

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
