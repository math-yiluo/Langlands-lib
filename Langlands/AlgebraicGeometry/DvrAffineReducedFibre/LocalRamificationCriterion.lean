import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.GenericFibreBaseChange
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.NormalizationTensorLocalization
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.UniformizerCriterion

/-! # Applying local uniformizer tests to the normalized base change -/

open IsLocalRing TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

private def atPrimeEquivOfEq {C : Type*} [CommRing C] (p q : Ideal C) [p.IsPrime]
    [q.IsPrime] (h : p = q) : Localization.AtPrime p ≃ₐ[C] Localization.AtPrime q := by
  subst q
  exact AlgEquiv.refl

private theorem span_scalar_eq_maximal_of_algEquiv {C A B : Type*} [CommRing C]
    [CommRing A] [IsLocalRing A] [Algebra C A] [CommRing B] [IsLocalRing B] [Algebra C B]
    (e : A ≃ₐ[C] B) (a : C)
    (h : Ideal.span {algebraMap C B a} = maximalIdeal B) :
    Ideal.span {algebraMap C A a} = maximalIdeal A := by
  have he : e.symm.toRingHom (algebraMap C B a) = algebraMap C A a := e.symm.commutes a
  have hg := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span, Set.image_singleton, he] at hg
  exact hg.trans (IsLocalRing.map_ringEquiv_maximalIdeal e.symm.toRingEquiv)

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

/-- The integral closure after localizing the original algebra at a prime and
then computing the normalization of the extended base. -/
abbrev localTensorNormalization (p : Ideal B) [p.IsPrime] : Type _ :=
  letI : Algebra (Localization.AtPrime p ⊗[B] D) (Localization.AtPrime p ⊗[B] H) :=
    tensorBaseChangeAlgebra B (Localization.AtPrime p) D (B := H)
  integralClosure (Localization.AtPrime p ⊗[B] D) (Localization.AtPrime p ⊗[B] H)

local notation "Cₚ" p => localTensorNormalization R S B G p

private theorem scalarIntegral_normalizationTensor [Algebra.IsIntegral R S] :
    Algebra.IsIntegral B C := by
  have : Algebra.IsIntegral B D := by
    constructor
    intro x
    let e := Algebra.TensorProduct.commRight R B S
    rw [← e.apply_symm_apply x]
    exact (Algebra.IsIntegral.isIntegral (e.symm x)).map e
  exact ⟨fun x => isIntegral_trans (R := B) (A := D) x (Algebra.IsIntegral.isIntegral x)⟩

private theorem algebraMap_base_to_tensorNormalization (r : R) :
    algebraMap B C (algebraMap R B r) = algebraMap S C (algebraMap R S r) := by
  apply Subtype.ext
  change (1 : S) ⊗ₜ[R] algebraMap B G (algebraMap R B r) = algebraMap R S r ⊗ₜ[R] (1 : G)
  rw [← IsScalarTower.algebraMap_apply R B G]
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) r).symm

variable [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    [IsLocalHom (algebraMap R S)]

private theorem span_baseUniformizer_le {π : R} (hπ : Irreducible π) {t : S} (ht : Irreducible t) :
    Ideal.span {algebraMap B C (algebraMap R B π)} ≤ Ideal.span {algebraMap S C t} := by
  rw [algebraMap_base_to_tensorNormalization R S B G]
  rw [Ideal.span_singleton_le_iff_mem]
  have h : algebraMap R S π ∈ maximalIdeal S := by
    have hmap : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
      ((local_hom_TFAE (algebraMap R S)).out 1 3 rfl rfl).mp inferInstance
    exact hmap (Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq.symm ▸ Ideal.mem_span_singleton_self π))
  have h' := Ideal.mem_map_of_mem (algebraMap S C) h
  simpa only [ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] using h'

private theorem minimalPrime_baseUniformizer_of_minimalPrime_quotient
    (hinj : Function.Injective (algebraMap R S)) {π : R} (hπ : Irreducible π)
    {t : S} (ht : Irreducible t) (Q : Ideal C) [Q.IsPrime]
    (hQ : (Ideal.span {algebraMap S C t}).IsMinimalPrime Q) :
    ((Ideal.span {algebraMap R B π}).map (algebraMap B C)).IsMinimalPrime Q := by
  rw [Ideal.map_span, Set.image_singleton]
  refine ⟨⟨inferInstance, (span_baseUniformizer_le R S B G hπ ht).trans hQ.le⟩, ?_⟩
  intro P hP hle
  have hpπ : algebraMap B C (algebraMap R B π) ∈ P := hP.2 (Ideal.mem_span_singleton_self _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ hinj).mpr hπ.ne_zero) ht
  rw [algebraMap_base_to_tensorNormalization R S B G, hu, map_mul, map_pow,
    Ideal.unit_mul_mem_iff_mem P (u.isUnit.map (algebraMap S C))] at hpπ
  exact hQ.2 ⟨hP.1, P.span_singleton_le_iff_mem.mpr (hP.1.mem_of_pow_mem n hpπ)⟩ hle

variable [Algebra.IsIntegral R S] [Module.Flat R S] [Module.Flat B G]

set_option maxHeartbeats 1000000 in
/-- For the normalized tensor base change, it suffices to test the uniformizer
in the local normalizations at the primes minimal over the original uniformizer. -/
theorem baseUniformizerAtGenericPoints_of_localTests
    (hinj : Function.Injective (algebraMap R S)) {π : R} (hπ : Irreducible π)
    {t : S} (ht : Irreducible t)
    (hNormal : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hLocal : ∀ (p : Ideal B) [p.IsPrime], (Ideal.span {algebraMap R B π}).IsMinimalPrime p →
      ∀ (J : Ideal (Cₚ p)) (hJ : J.IsMaximal),
        letI : J.IsPrime := hJ.isPrime
        letI : Algebra C (Cₚ p) :=
          (integralClosureTensorLocalizationMap B D H p.primeCompl).toRingHom.toAlgebra
        letI : Algebra C (Localization.AtPrime J) := Algebra.compHom _ (algebraMap C (Cₚ p))
        Ideal.span {algebraMap C (Localization.AtPrime J) (algebraMap S C t)} =
          maximalIdeal (Localization.AtPrime J)) :
    BaseUniformizerAtGenericPoints S C t := by
  intro Q hQprime hQ
  have : Algebra.HasGoingDown B C := hasGoingDown_normalizationTensor R S B G hNormal
  have : Algebra.IsIntegral B C := scalarIntegral_normalizationTensor R S B G
  let p := Q.under B
  have hp : (Ideal.span {algebraMap R B π}).IsMinimalPrime p :=
    minimalPrime_under_of_hasGoingDown _ Q
      (minimalPrime_baseUniformizer_of_minimalPrime_quotient R S B G hinj hπ ht Q hQ)
  let M := Algebra.algebraMapSubmonoid C p.primeCompl
  let E := Cₚ p
  let : Algebra C E :=
    (integralClosureTensorLocalizationMap B D H p.primeCompl).toRingHom.toAlgebra
  have : IsLocalization M E := isLocalization_integralClosureTensorLocalization B D H p.primeCompl
  have hdisj : Disjoint (M : Set C) (Q : Set C) := by
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ hbQ
    exact hb hbQ
  let J := Q.map (algebraMap C E)
  have : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M E Q inferInstance hdisj
  have hJQ : J.under C = Q := IsLocalization.under_map_of_isPrime_disjoint M E inferInstance hdisj
  have hJ : J.IsMaximal := isMaximal_integralClosureTensorLocalization_of_under B D H p.primeCompl
    p rfl J (congrArg (Ideal.under B) hJQ)
  let T := Localization.AtPrime J
  let : CommRing T := OreLocalization.instCommRing (R := E) (S := J.primeCompl)
  let : CommRing (Localization.AtPrime Q) :=
    OreLocalization.instCommRing (R := ↥C) (S := Q.primeCompl)
  let : Algebra C T := Algebra.compHom T (algebraMap C E)
  let T₀ := Localization.AtPrime (J.under C)
  let e₁ : Localization.AtPrime Q ≃ₐ[C] T₀ := atPrimeEquivOfEq Q (J.under C) hJQ.symm
  let e₂ : T₀ ≃ₐ[C] T := integralClosureTensorLocalizationAtPrimeEquiv B D H p.primeCompl J
  let e := e₁.trans e₂
  have hT : Ideal.span {algebraMap C T (algebraMap S C t)} = maximalIdeal T := hLocal p hp J hJ
  have hgen := span_scalar_eq_maximal_of_algEquiv (A := Localization.AtPrime Q) (B := T)
    e (algebraMap S C t) hT
  exact (congrArg (fun x : Localization.AtPrime Q => Ideal.span {x})
    (IsScalarTower.algebraMap_apply S C (Localization.AtPrime Q) t)).trans hgen

end TensorNormalization

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
