import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FiniteExtensionSolutions
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.VerticalDvr

/-! # Assembling local finite solutions over a complete DVR -/

open IsLocalRing TensorProduct

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- The local ring at a prime minimal over an ideal. -/
abbrev minimalPrimeLocalRing {B : Type*} [CommRing B] {I : Ideal B}
    (p : I.minimalPrimes) : Type _ :=
  @Localization.AtPrime B _ p.1 p.2.isPrime

section LocalTest

variable (R S B G Q : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [CommRing B] [Algebra R B]
    [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]
    (p : Ideal B) [p.IsPrime] [CommRing Q] [Algebra R Q] [IsDomain Q]
    [IsDiscreteValuationRing Q] [IsLocalHom (algebraMap R Q)]

local notation "D" => S ⊗[R] Q
local notation "H" => D ⊗[S] FractionRing S
local notation "C" => integralClosure D H
local instance : CommRing C := @Subalgebra.toCommRing D H _ _ _ C

set_option maxHeartbeats 1000000 in
private theorem localUniformizerTest_of_reduced_generic_normalization
    (hinjS : Function.Injective (algebraMap R S)) (hinjQ : Function.Injective (algebraMap R Q))
    {t : S} (ht : Irreducible t) (e : localTensorNormalization R S B G p ≃+* C)
    (he : e (localTensorNormalizationBaseMap R S B G p t) = algebraMap S C t)
    (hred : IsReduced (ResidueField S ⊗[S] C)) :
    LocalUniformizerTest R S B G t p := by
  let x := localTensorNormalizationBaseMap R S B G p t
  have h : UniformizerAtMaximalLocalizations C (algebraMap S C t) :=
    uniformizerAtMaximalLocalizations_of_reduced_normalizedResidue R S Q hinjS hinjQ ht hred
  have hx : UniformizerAtMaximalLocalizations C (e x) :=
    (congrArg (UniformizerAtMaximalLocalizations C) he).mpr h
  let E := localTensorNormalization R S B G p
  let : CommRing E := inferInstanceAs (CommRing (localTensorNormalization R S B G p))
  have hf := @uniformizerAtMaximalLocalizations_iff E _ (↥C) _ e x
  exact hf.mp hx

end LocalTest

section VerticalLocalRing

variable (R B G : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [Algebra R B]
    [CommRing G] [Algebra B G]

omit [IsDiscreteValuationRing R] in
private theorem algebraMap_mem_nonZeroDivisors_of_genericLocalization
    (hBG : Function.Injective (algebraMap B G))
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G)
    {a : R} (ha : a ≠ 0) :
    algebraMap R B a ∈ nonZeroDivisors B := by
  have hunit : IsUnit (algebraMap B G (algebraMap R B a)) :=
    IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G
      ⟨algebraMap R B a, Algebra.mem_algebraMapSubmonoid_of_mem ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩⟩
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  apply hBG
  have he := congrArg (algebraMap B G) hx
  rw [map_mul, map_zero] at he
  simpa only [map_zero] using hunit.mul_right_eq_zero.mp he

private theorem localHom_and_injective_at_verticalPrime {π : R} (hπ : Irreducible π)
    (hregular : ∀ {a : R}, a ≠ 0 → algebraMap R B a ∈ nonZeroDivisors B)
    (p : Ideal B) [p.IsPrime] (hp : (Ideal.span {algebraMap R B π}).IsMinimalPrime p) :
    IsLocalHom (algebraMap R (Localization.AtPrime p)) ∧
      Function.Injective (algebraMap R (Localization.AtPrime p)) := by
  let Q := Localization.AtPrime p
  have hmem : algebraMap R Q π ∈ maximalIdeal Q := by
    rw [IsScalarTower.algebraMap_apply R B Q]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Q p _).mpr
      (hp.le (Ideal.mem_span_singleton_self _))
  constructor
  · apply ((local_hom_TFAE (algebraMap R Q)).out 1 3 rfl rfl).mpr
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hmem
  · apply (injective_iff_map_eq_zero (algebraMap R Q)).mpr
    intro a ha
    by_contra hn
    have hreg := IsLocalization.nonZeroDivisors_le_comap p.primeCompl Q (hregular hn)
    rw [IsScalarTower.algebraMap_apply R B Q] at ha
    exact nonZeroDivisors.ne_zero hreg ha

end VerticalLocalRing

section VerticalFibre

variable (R S B G : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [CommRing B] [Algebra R B] [IsNoetherianRing B]
    [CommRing G] [Algebra R G] [Algebra B G] [IsScalarTower R B G]
    (p : Ideal B) [p.IsPrime]

local notation "Q" => Localization.AtPrime p
local notation "D" => S ⊗[R] Q
local notation "H" => D ⊗[S] FractionRing S
local notation "C" => integralClosure D H
local instance : CommRing Q := OreLocalization.instCommRing (R := B) (S := p.primeCompl)
local instance : CommRing C := @Subalgebra.toCommRing D H _ _ _ C

set_option maxHeartbeats 1500000 in
private theorem localUniformizerTest_of_vertical_reducedResidue
    (hBG : Function.Injective (algebraMap B G))
    (hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) G)
    (hinjS : Function.Injective (algebraMap R S)) {π : R} (hπ : Irreducible π)
    (hp : (Ideal.span {algebraMap R B π}).IsMinimalPrime p)
    (hnormal : IsDomain Q ∧ IsIntegrallyClosed Q) {t : S} (ht : Irreducible t)
    (hred : IsReduced (ResidueField S ⊗[S] C)) :
    LocalUniformizerTest R S B G t p := by
  have hreg {a : R} (ha : a ≠ 0) : algebraMap R B a ∈ nonZeroDivisors B :=
    algebraMap_mem_nonZeroDivisors_of_genericLocalization R B G hBG hloc ha
  obtain ⟨hDom, hClosed⟩ := hnormal
  have hDvr : IsDiscreteValuationRing Q :=
    isDiscreteValuationRing_atPrime_of_minimal_principal (hreg hπ.ne_zero) p hp
  obtain ⟨hHom, hInj⟩ := localHom_and_injective_at_verticalPrime R B hπ
    (fun ha => hreg ha) p hp
  let e := localTensorNormalizationGenericEquiv R S B G p hinjS hloc
  have he := localTensorNormalizationGenericEquiv_baseMap R S B G p hinjS hloc t
  exact localUniformizerTest_of_reduced_generic_normalization R S B G Q p hinjS hInj ht e he hred

end VerticalFibre

section CompleteBase

variable (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FiniteType R A]
    [Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A)]

local notation "K" => FractionRing R
local notation "G" => A ⊗[R] K
local notation "N" => integralClosure A G
local notation "I" π => Ideal.span {algebraMap R N π}

set_option maxHeartbeats 1500000 in
/-- A finite solution at each generic point of the original normalized special
fibre gives a faithfully flat DVR extension with finite normalization and all
field fibres reduced. -/
theorem exists_reduced_fibres_of_local_finiteExtensions {π : R} (hπ : Irreducible π)
    (hLocal : ∀ (p : (I π).minimalPrimes),
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
        (_ : IsScalarTower R K L) (_ : FiniteDimensional K L),
        IsReduced (finiteExtensionNormalizedResidue R (minimalPrimeLocalRing p) L)) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S),
      Module.FaithfullyFlat R S ∧
        Module.Finite (S ⊗[R] A) (integralClosure (S ⊗[R] A) ((S ⊗[R] A) ⊗[S] FractionRing S)) ∧
        ∀ (F : Type u) [Field F] [Algebra S F],
          IsReduced (F ⊗[S] integralClosure (S ⊗[R] A) ((S ⊗[R] A) ⊗[S] FractionRing S)) := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : Module.Finite A N := finite_integralClosure_genericFibre_of_completeDvr R A
  have : IsNoetherianRing N := IsNoetherianRing.of_finite A N
  let ι := (I π).minimalPrimes
  let B (p : ι) := minimalPrimeLocalRing p
  let : Fintype ι := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (I π)).fintype
  let : ∀ p, CommRing (B p) := fun p => by
    have : p.1.IsPrime := p.2.isPrime
    exact OreLocalization.instCommRing (R := ↥N) (S := p.1.primeCompl)
  let : ∀ p, Algebra R (B p) := fun p => by
    have : p.1.IsPrime := p.2.isPrime
    exact inferInstanceAs (Algebra R (Localization.AtPrime p.1))
  obtain ⟨L, _, _, _, _, _, hL⟩ := exists_common_finiteExtensionNormalizedResidue R B hLocal
  let S := integralClosure R L
  obtain ⟨hDvr, hComplete⟩ := isDiscreteValuationRing_and_isAdicComplete_of_finiteExtension R L
  have : Module.FaithfullyFlat R S :=
    Langlands.CommutativeAlgebra.DvrFiniteSeparableExtension.faithfullyFlat R L
  have : Module.Finite R S := finite_integralClosure_of_finiteExtension R L
  have : IsLocalHom (algebraMap R S) := (inferInstance : Algebra.IsIntegral R S).isLocalHom
  have : IsAlgClosed (ResidueField S) :=
    IsAlgClosed.of_ringEquiv (ResidueField R) (ResidueField S) (residueEquiv_of_finiteExtension R L)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hinjS := FaithfulSMul.algebraMap_injective R S
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid N (nonZeroDivisors R)) G :=
    isLocalization_integralClosure_genericFibre R A
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  apply finite_normalization_and_reduced_fibres_of_localUniformizerTests R S A hinjS hπ ht
  intro p hpPrime hp
  let q : ι := ⟨p, hp⟩
  have hred := hL q
  have hnorm := normal_localizations_genericNormalization R A p
  refine @localUniformizerTest_of_vertical_reducedResidue R S N G
    _ _ _ _ _ hDvr _ _ _ _ _ _ _ _ _ _ p hpPrime
    Subtype.val_injective hloc hinjS π hπ hp hnorm t ht ?_
  exact hred

end CompleteBase

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
