/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Ordinary étale locally closed exceptional restriction and coefficient change

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
`thm-coef-finite-hom.md`, proof paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek).

The closed exceptional functor is the ambient ordinary unbounded étale right adjoint.
All scalar functors are ordinary uncompleted scalar extension. The comparisons below
are constructed from the published coefficient map and the specified adjunction counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The ordinary closed exceptional right adjoint supplied by
lemma-local-cohomology-right-adjoint--1. Source: blueprint
lemma-change-coefficients-internal-hom--1, paragraph 3 (blueprint:
lem-coef-etale-locally-closed-shriek). -/
abbrev etaleShriekClosedExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] :=
  (R(lowerStar (ModuleCat.{u + 1} A) g)).rightAdjoint

/-- The fixed ordinary closed exceptional adjunction.
Source: blueprint lemma-change-coefficients-internal-hom--1, paragraph 3
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekClosedAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] :
    R(lowerStar (ModuleCat.{u + 1} A) g) ⊣ etaleShriekClosedExceptional A g :=
  Adjunction.ofIsLeftAdjoint _

/-- The composite ordinary adjunction `g_* j_! ⊣ j^* Rg^!`, with its pasted counit.
This is the locally closed case of the recorded compact-support construction.
Source: blueprint lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekLocallyClosedAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] :
    derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat.{u + 1} A) g) ⊣
      etaleShriekClosedExceptional A g ⋙ derivedRestriction (A := A) j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (etaleShriekClosedAdjunction A g)

/-- Inverse of the actual coefficient comparison on its isomorphism locus.
The zero extension elsewhere merely makes the formula total; the theorem explicitly
asserts invertibility of this comparison on every input on which it uses the inverse.
Source: blueprint lemma-change-coefficients-internal-hom--1, paragraph 3
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekDirectInverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z X : Scheme.{u}} (g : Z ⟶ X) (N : DerivedCategoryModule A Z) :
    (R(lowerStar (ModuleCat.{u + 1} B) g)).obj ((scalarExtension φ Z).obj N) ⟶
      (scalarExtension φ X).obj ((R(lowerStar (ModuleCat.{u + 1} A) g)).obj N) :=
  open Classical in
  if h : IsIso (finiteCoefficientDirectImageMap φ g N) then
    @inv _ _ _ _ (finiteCoefficientDirectImageMap φ g N) h
  else 0

/-- The specified closed coefficient map: the exceptional-adjunction transpose of
`c_g⁻¹` followed by scalar extension of the A-exceptional counit.
Source: blueprint lemma-change-coefficients-internal-hom--1, paragraph 3
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekClosedCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).obj ((etaleShriekClosedExceptional A g).obj M) ⟶
      (etaleShriekClosedExceptional B g).obj ((scalarExtension φ X).obj M) :=
  (etaleShriekClosedAdjunction B g).homEquiv _ _
    (etaleShriekDirectInverse φ g ((etaleShriekClosedExceptional A g).obj M) ≫
      (scalarExtension φ X).map ((etaleShriekClosedAdjunction A g).counit.app M))

/-- Restrict the closed coefficient map, with the canonical scalar/restriction
identification. This is precisely the map `b_s = j^* b_g` under that identification.
Source: blueprint lemma-change-coefficients-internal-hom--1, paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekLocallyClosedCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] (M : DerivedCategoryModule A X) :
    (scalarExtension φ S).obj
        ((derivedRestriction (A := A) j).obj ((etaleShriekClosedExceptional A g).obj M)) ⟶
      (derivedRestriction (A := B) j).obj
        ((etaleShriekClosedExceptional B g).obj ((scalarExtension φ X).obj M)) :=
  (openScalarRestriction φ j).hom.app ((etaleShriekClosedExceptional A g).obj M) ≫
    (derivedRestriction (A := B) j).map (etaleShriekClosedCoefficientMap φ g M)

/-- The fixed compact-support coefficient map `g_*(q_j) ∘ c_{g,j_!P}`.
The open comparison is the published natural isomorphism normalized to the identity
on the open stratum, not an arbitrary choice of scalar comparison.
Source: blueprint lemma-change-coefficients-internal-hom--1, paragraph 4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekLocallyClosedSupportMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (P : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) g)).obj ((derivedExtension (A := A) j).obj P)) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) g)).obj
        ((derivedExtension (A := B) j).obj ((scalarExtension φ S).obj P)) :=
  finiteCoefficientDirectImageMap φ g ((derivedExtension (A := A) j).obj P) ≫
    (R(lowerStar (ModuleCat.{u + 1} B) g)).map ((openScalarExtension φ j).hom.app P)

/-- All clauses of the ordinary étale locally closed comparison, including naturality
on the specified finite-Tor constructible domains and the counit identity.
The final theorem supplies the existing finite-stage predicate as `ctf`; this parameter
only packages the assertions and introduces no alternative constructibility definition.
Source: blueprint lemma-change-coefficients-internal-hom--1, paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def EtaleLocallyClosedShriekComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (ctf : ∀ T : Scheme.{u}, ObjectProperty (DerivedCategoryModule A T))
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] : Prop :=
  (∀ N : DerivedCategoryModule A Z, ctf Z N →
    IsIso (finiteCoefficientDirectImageMap φ g N)) ∧
  (∀ M : DerivedCategoryModule A X, ctf X M →
    ctf Z ((etaleShriekClosedExceptional A g).obj M) ∧
    ctf S
      ((derivedRestriction (A := A) j).obj ((etaleShriekClosedExceptional A g).obj M)) ∧
    IsIso (finiteCoefficientDirectImageMap φ g ((etaleShriekClosedExceptional A g).obj M)) ∧
    IsIso (etaleShriekClosedCoefficientMap φ g M) ∧
    IsIso (etaleShriekLocallyClosedCoefficientMap φ g j M) ∧
    etaleShriekLocallyClosedSupportMap φ g j
        ((derivedRestriction (A := A) j).obj ((etaleShriekClosedExceptional A g).obj M)) ≫
      (derivedExtension (A := B) j ⋙ R(lowerStar (ModuleCat.{u + 1} B) g)).map
        (etaleShriekLocallyClosedCoefficientMap φ g j M) ≫
      (etaleShriekLocallyClosedAdjunction B g j).counit.app ((scalarExtension φ X).obj M) =
        (scalarExtension φ X).map ((etaleShriekLocallyClosedAdjunction A g j).counit.app M)) ∧
  (∀ P : DerivedCategoryModule A S, ctf S P →
    IsIso (etaleShriekLocallyClosedSupportMap φ g j P)) ∧
  (∀ (M N : DerivedCategoryModule A X),
    ctf X M → ctf X N →
    ∀ f : M ⟶ N,
      (etaleShriekClosedExceptional A g ⋙ scalarExtension φ Z).map f ≫
          etaleShriekClosedCoefficientMap φ g N =
        etaleShriekClosedCoefficientMap φ g M ≫
          (scalarExtension φ X ⋙ etaleShriekClosedExceptional B g).map f) ∧
  (∀ (M N : DerivedCategoryModule A X),
    ctf X M → ctf X N →
    ∀ f : M ⟶ N,
      (etaleShriekClosedExceptional A g ⋙ derivedRestriction (A := A) j ⋙
          scalarExtension φ S).map f ≫ etaleShriekLocallyClosedCoefficientMap φ g j N =
        etaleShriekLocallyClosedCoefficientMap φ g j M ≫
          (scalarExtension φ X ⋙ etaleShriekClosedExceptional B g ⋙
            derivedRestriction (A := B) j).map f) ∧
  (∀ (P Q : DerivedCategoryModule A S),
    ctf S P → ctf S Q →
    ∀ f : P ⟶ Q,
      (derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat.{u + 1} A) g) ⋙
          scalarExtension φ X).map f ≫ etaleShriekLocallyClosedSupportMap φ g j Q =
        etaleShriekLocallyClosedSupportMap φ g j P ≫
          (scalarExtension φ S ⋙ derivedExtension (A := B) j ⋙
            R(lowerStar (ModuleCat.{u + 1} B) g)).map f) ∧
  (∀ M : DerivedCategoryModule A X,
    (etaleShriekLocallyClosedAdjunction A g j).counit.app M =
      (R(lowerStar (ModuleCat.{u + 1} A) g)).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).counit.app ((etaleShriekClosedExceptional A g).obj M)) ≫
        (etaleShriekClosedAdjunction A g).counit.app M)

private lemma coefficient_isUnit_characteristic
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) : IsUnit (D.p : ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hv : Padic.coefficientExtensionAbsoluteValue l E (D.p : E) = 1 := by
    have he := spectralNorm_extends (K := Padic l) (L := E) (D.p : Padic l)
    have hn : ‖(D.p : Padic l)‖ = 1 := Padic.norm_natCast_eq_one_iff.2
      ((Nat.coprime_primes (Fact.out : l.Prime) D.prime).2 hl)
    change spectralNorm (Padic l) E (D.p : E) = 1
    simpa only [map_natCast, hn] using he
  have hu : IsUnit (D.p : Padic.coefficientExtensionIntegers l E) :=
    (h.2.2.1 _).2 hv
  have hq : IsUnit (D.p : Padic.coefficientExtensionRing l E n) := by
    simpa using hu.map (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
  simpa using hq.map (ULift.ringEquiv.symm.toRingHom)

private lemma coefficient_hasInvertibleExponent
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) (aT : T ⟶ Spec (.of D.k)) :
    HasInvertibleExponent (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T := by
  classical
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let : Finite A := Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap
    (algebraMap D.k₀ D.k).injective D.p
  let : Invertible (D.p : A) := (coefficient_isUnit_characteristic D l hl E n).invertible
  let : HasInvertibleExponent A (Spec (.of D.k)) :=
    HasInvertibleExponent.spec_of_charP A D.p
  exact HasInvertibleExponent.of_hom aT

private lemma boundedConstructible_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : DerivedCategoryModule A T) :
    DerivedCategory.isBoundedConstructible A T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun q hq ↦ hz q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun q hq ↦ hz q (.inr hq)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hc q), min a b, max a b, (min_le_left a b).trans (le_max_left a b), ?_⟩
    intro q hq
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q
        (hq.trans_le (min_le_left a b))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q
        ((le_max_right a b).trans_lt hq)

private lemma finiteTor_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : DerivedCategoryModule A T) :
    (DerivedCategory.isBoundedConstructible A T K ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b K) ↔
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, ht⟩
    exact ⟨(boundedConstructible_iff A T K).1 hc, a, b,
      DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht⟩
  · rintro ⟨hc, a, b, ht⟩
    refine ⟨(boundedConstructible_iff A T K).2 hc, min a b, max a b,
      (min_le_left a b).trans (le_max_left a b), ?_⟩
    exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (DerivedCategory.torAmplitudeIn.mono (min_le_left a b) (le_max_right a b) ht)

private lemma finiteTor_restriction (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : DerivedCategoryModule A T)
    (hK : DerivedCategory.isBoundedConstructible A T K ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b K) :
    DerivedCategory.isBoundedConstructible A U ((derivedRestriction (A := A) j).obj K) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A U a b
        ((derivedRestriction (A := A) j).obj K) := by
  apply (finiteTor_iff A U _).2
  obtain ⟨hc, a, b, ht⟩ := constructibleFiniteTor_leftDerivedUpperStar
    (ModuleCat.{u + 1} A) j ((finiteTor_iff A T K).1 hK)
  let e := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).app K
  exact ⟨(DerivedCategory.boundedConstructible _ U).prop_of_iso e hc, a, b,
    (DerivedCategory.torAmplitudeIn _ U a b).prop_of_iso e ht⟩

private lemma finiteTor_extension (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategoryModule A U)
    (hK : DerivedCategory.isBoundedConstructible A U K ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A U a b K) :
    DerivedCategory.isBoundedConstructible A T ((derivedExtension (A := A) j).obj K) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b
        ((derivedExtension (A := A) j).obj K) := by
  obtain ⟨hc, a, b, _, ht⟩ := hK
  have ht' := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht
  have h := constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
    A j a b ⟨⟨(boundedConstructible_iff A U K).1 hc,
      _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht'⟩, ht'⟩
  exact (finiteTor_iff A T _).2 ⟨h.1.1, a, b, h.2⟩

private lemma finiteTor_closedExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] {Z T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasInvertibleExponent A T] (g : Z ⟶ T) [IsClosedImmersion g]
    [HasCompactification g]
    (K : DerivedCategoryModule A T)
    (hK : DerivedCategory.isBoundedConstructible A T K ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b K) :
    DerivedCategory.isBoundedConstructible A Z
        ((etaleShriekClosedExceptional A g).obj K) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A Z a b
        ((etaleShriekClosedExceptional A g).obj K) := by
  let e := ((etaleShriekClosedAdjunction A g).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) g).symm)
    |>.rightAdjointUniq (rightDerivedUpperShriekAdjunction A g)
  apply (finiteTor_iff A Z _).2
  obtain ⟨hc, a, b, ht⟩ := constructibleFiniteTor_rightDerivedUpperShriek A aT g
    ((finiteTor_iff A T K).1 hK)
  exact ⟨(DerivedCategory.boundedConstructible _ Z).prop_of_iso (e.app K).symm hc,
    a, b, (DerivedCategory.torAmplitudeIn _ Z a b).prop_of_iso (e.app K).symm ht⟩

private lemma directInverse_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) (N : DerivedCategoryModule A Z)
    [IsIso (finiteCoefficientDirectImageMap φ g N)] :
    etaleShriekDirectInverse φ g N = inv (finiteCoefficientDirectImageMap φ g N) := by
  simp only [etaleShriekDirectInverse, dite_eq_left (inferInstance : IsIso _)]

private lemma closedCoefficient_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (M : DerivedCategoryModule A X)
    [IsIso (finiteCoefficientDirectImageMap φ g
      ((etaleShriekClosedExceptional A g).obj M))] :
    finiteCoefficientDirectImageMap φ g ((etaleShriekClosedExceptional A g).obj M) ≫
        (R(lowerStar (ModuleCat.{u + 1} B) g)).map
          (etaleShriekClosedCoefficientMap φ g M) ≫
        (etaleShriekClosedAdjunction B g).counit.app ((scalarExtension φ X).obj M) =
      (scalarExtension φ X).map ((etaleShriekClosedAdjunction A g).counit.app M) := by
  have h := ((etaleShriekClosedAdjunction B g).homEquiv _ _).symm_apply_apply
    (etaleShriekDirectInverse φ g ((etaleShriekClosedExceptional A g).obj M) ≫
      (scalarExtension φ X).map ((etaleShriekClosedAdjunction A g).counit.app M))
  rw [Adjunction.homEquiv_symm_apply] at h
  change (R(lowerStar (ModuleCat.{u + 1} B) g)).map
      (etaleShriekClosedCoefficientMap φ g M) ≫ _ = _ at h
  dsimp only [Functor.id_obj] at h
  rw [h, directInverse_eq]
  simp

private lemma closedCoefficient_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    {M N : DerivedCategoryModule A X}
    [IsIso (finiteCoefficientDirectImageMap φ g
      ((etaleShriekClosedExceptional A g).obj M))]
    [IsIso (finiteCoefficientDirectImageMap φ g
      ((etaleShriekClosedExceptional A g).obj N))] (f : M ⟶ N) :
    (etaleShriekClosedExceptional A g ⋙ scalarExtension φ Z).map f ≫
        etaleShriekClosedCoefficientMap φ g N =
      etaleShriekClosedCoefficientMap φ g M ≫
        (scalarExtension φ X ⋙ etaleShriekClosedExceptional B g).map f := by
  apply (etaleShriekClosedAdjunction B g).homEquiv_naturality_left_square
  change (R(lowerStar (ModuleCat.{u + 1} B) g)).map
      ((scalarExtension φ Z).map ((etaleShriekClosedExceptional A g).map f)) ≫
      (etaleShriekDirectInverse φ g ((etaleShriekClosedExceptional A g).obj N) ≫
        (scalarExtension φ X).map ((etaleShriekClosedAdjunction A g).counit.app N)) =
    (etaleShriekDirectInverse φ g ((etaleShriekClosedExceptional A g).obj M) ≫
      (scalarExtension φ X).map ((etaleShriekClosedAdjunction A g).counit.app M)) ≫
        (scalarExtension φ X).map f
  rw [directInverse_eq, directInverse_eq]
  have hc := finiteCoefficientDirectImageMap_naturality φ g
    ((etaleShriekClosedExceptional A g).map f)
  have he := (etaleShriekClosedAdjunction A g).counit_naturality f
  apply (cancel_epi (finiteCoefficientDirectImageMap φ g
    ((etaleShriekClosedExceptional A g).obj M))).1
  rw [← Category.assoc, ← Category.assoc, ← hc]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp, he, Functor.map_comp]

private lemma locallyClosedCoefficient_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    {S : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j] {M N : DerivedCategoryModule A X}
    [IsIso (finiteCoefficientDirectImageMap φ g
      ((etaleShriekClosedExceptional A g).obj M))]
    [IsIso (finiteCoefficientDirectImageMap φ g
      ((etaleShriekClosedExceptional A g).obj N))] (f : M ⟶ N) :
    (etaleShriekClosedExceptional A g ⋙ derivedRestriction (A := A) j ⋙
        scalarExtension φ S).map f ≫ etaleShriekLocallyClosedCoefficientMap φ g j N =
      etaleShriekLocallyClosedCoefficientMap φ g j M ≫
        (scalarExtension φ X ⋙ etaleShriekClosedExceptional B g ⋙
          derivedRestriction (A := B) j).map f := by
  dsimp only [etaleShriekLocallyClosedCoefficientMap, Functor.comp_map]
  have hn := (openScalarRestriction φ j).hom.naturality
    ((etaleShriekClosedExceptional A g).map f)
  dsimp only [Functor.comp_map] at hn
  have hb := closedCoefficient_naturality φ g f
  dsimp only [Functor.comp_map] at hb
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, hb,
    Functor.map_comp, Category.assoc]

private lemma support_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X)
    {S : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j] {P Q : DerivedCategoryModule A S} (f : P ⟶ Q) :
    (derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat.{u + 1} A) g) ⋙
        scalarExtension φ X).map f ≫ etaleShriekLocallyClosedSupportMap φ g j Q =
      etaleShriekLocallyClosedSupportMap φ g j P ≫
        (scalarExtension φ S ⋙ derivedExtension (A := B) j ⋙
          R(lowerStar (ModuleCat.{u + 1} B) g)).map f := by
  dsimp only [etaleShriekLocallyClosedSupportMap, Functor.comp_map]
  rw [← Category.assoc, finiteCoefficientDirectImageMap_naturality, Category.assoc,
    ← Functor.map_comp]
  have h := (openScalarExtension φ j).hom.naturality f
  dsimp only [Functor.comp_map] at h
  rw [h, Functor.map_comp, Category.assoc]

private lemma locallyClosedCoefficient_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    {S : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j] (M : DerivedCategoryModule A X)
    [IsIso (finiteCoefficientDirectImageMap φ g
      ((etaleShriekClosedExceptional A g).obj M))] :
    etaleShriekLocallyClosedSupportMap φ g j
        ((derivedRestriction (A := A) j).obj ((etaleShriekClosedExceptional A g).obj M)) ≫
      (derivedExtension (A := B) j ⋙ R(lowerStar (ModuleCat.{u + 1} B) g)).map
        (etaleShriekLocallyClosedCoefficientMap φ g j M) ≫
      (etaleShriekLocallyClosedAdjunction B g j).counit.app ((scalarExtension φ X).obj M) =
        (scalarExtension φ X).map ((etaleShriekLocallyClosedAdjunction A g j).counit.app M) := by
  let N := (etaleShriekClosedExceptional A g).obj M
  let N' := (etaleShriekClosedExceptional B g).obj ((scalarExtension φ X).obj M)
  let b := etaleShriekClosedCoefficientMap φ g M
  let εA := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).counit.app N
  let εB := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).counit.app N'
  have hOpen : (openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj N) ≫
      (derivedExtension (A := B) j).map (etaleShriekLocallyClosedCoefficientMap φ g j M) ≫
      εB = (scalarExtension φ Z).map εA ≫ b := by
    dsimp only [etaleShriekLocallyClosedCoefficientMap]
    rw [Functor.map_comp, Category.assoc]
    have hn := (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).counit_naturality b
    rw [← Category.assoc, hn, ← Category.assoc]
    simpa only [Category.assoc] using
      congrArg (fun h ↦ h ≫ b) ((etaleOpenTensorComparisons φ j).counit N)
  have hc := finiteCoefficientDirectImageMap_naturality φ g εA
  simp only [etaleShriekLocallyClosedSupportMap, etaleShriekLocallyClosedAdjunction,
    Adjunction.comp_counit_app, Functor.comp_map]
  change (finiteCoefficientDirectImageMap φ g _ ≫
      (R(lowerStar (ModuleCat.{u + 1} B) g)).map
        ((openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj N))) ≫
      (R(lowerStar (ModuleCat.{u + 1} B) g)).map
        ((derivedExtension (A := B) j).map (etaleShriekLocallyClosedCoefficientMap φ g j M)) ≫
      (R(lowerStar (ModuleCat.{u + 1} B) g)).map εB ≫
      (etaleShriekClosedAdjunction B g).counit.app _ = _
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hOpen,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hc, closedCoefficient_counit, ← Functor.map_comp]

private lemma closedCoefficient_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    {U : Scheme.{u}} (v : U ⟶ X) [IsOpenImmersion v]
    (hgv : Set.range g.base = (Set.range v.base)ᶜ)
    (M : DerivedCategoryModule A X)
    [IsIso (finiteCoefficientDirectImageMap φ g
      ((etaleShriekClosedExceptional A g).obj M))]
    [IsIso (finiteCoefficientDirectImageMap φ v ((derivedRestriction (A := A) v).obj M))] :
    IsIso (etaleShriekClosedCoefficientMap φ g M) := by
  let F := scalarExtension φ X
  let scalarAdj : F ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ :=
    Adjunction.ofIsRightAdjoint _
  let : F.CommShift ℤ :=
    scalarAdj.leftAdjointCommShift ℤ
  have : scalarAdj.CommShift ℤ := scalarAdj.commShift_of_rightAdjoint ℤ
  have : F.IsTriangulated := scalarAdj.isTriangulated_leftAdjoint
  let JA := derivedRestriction (A := A) v
  let JB := derivedRestriction (A := B) v
  let GA := R(lowerStar (ModuleCat.{u + 1} A) v)
  let GB := R(lowerStar (ModuleCat.{u + 1} B) v)
  let adjA := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v
  let adjB := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v
  let η := adjA.unit.app M
  let E := F.obj (GA.obj (JA.obj M))
  have hE : GB.essImage E :=
    ⟨(scalarExtension φ U).obj (JA.obj M),
      ⟨(asIso (finiteCoefficientDirectImageMap φ v (JA.obj M))).symm⟩⟩
  have hηE : IsIso (adjB.unit.app E) :=
    adjB.isIso_unit_app_iff_mem_essImage.2 hE
  have hJA : IsIso (JA.map η) := by
    have : IsIso adjA.counit := adjA.counit_isIso_of_R_fully_faithful
    change IsIso (JA.map (adjA.unit.app M))
    rw [← IsIso.inv_eq_of_inv_hom_id (adjA.left_triangle_components M)]
    infer_instance
  have hn := (openScalarRestriction φ v).hom.naturality η
  change (scalarExtension φ U).map (JA.map η) ≫
      (openScalarRestriction φ v).hom.app (GA.obj (JA.obj M)) =
    (openScalarRestriction φ v).hom.app M ≫ JB.map (F.map η) at hn
  have hJB : IsIso (JB.map (F.map η)) := by
    have heq : JB.map (F.map η) = (openScalarRestriction φ v).inv.app M ≫
        (scalarExtension φ U).map (JA.map η) ≫
          (openScalarRestriction φ v).hom.app (GA.obj (JA.obj M)) := by
      rw [hn]
      simp
    rw [heq]
    infer_instance
  let e : GB.obj (JB.obj (F.obj M)) ⟶ E :=
    GB.map (JB.map (F.map η)) ≫ inv (adjB.unit.app E)
  have he : IsIso e := by dsimp [e]; infer_instance
  have he_unit : adjB.unit.app (F.obj M) ≫ e = F.map η := by
    dsimp only [e]
    have hnat : F.map η ≫ adjB.unit.app E =
        adjB.unit.app (F.obj M) ≫ GB.map (JB.map (F.map η)) :=
      (adjB.unit_naturality (F.map η)).symm
    rw [← Category.assoc, ← hnat]
    simp
  obtain ⟨δA, hδA⟩ := exists_etale_closedSupportTriangle A g v hgv
  obtain ⟨δB, hδB⟩ := exists_etale_closedSupportTriangle B g v hgv
  let TA := F.mapTriangle.obj (Pretriangulated.Triangle.mk
    ((etaleShriekClosedAdjunction A g).counit.app M) η (δA.app M))
  let TB := Pretriangulated.Triangle.mk
    ((etaleShriekClosedAdjunction B g).counit.app (F.obj M))
    (adjB.unit.app (F.obj M)) (δB.app (F.obj M))
  have hTA : TA ∈ distTriang _ := F.map_distinguished _ (hδA M)
  have hTB : TB ∈ distTriang _ := hδB (F.obj M)
  have hsq : TA.mor₂ ≫ inv e = (𝟙 (F.obj M)) ≫ TB.mor₂ := by
    change F.map η ≫ inv e = (𝟙 _) ≫ adjB.unit.app (F.obj M)
    rw [← he_unit]
    simp
  obtain ⟨t, ht, ht₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    TA TB hTA hTB (𝟙 _) (inv e) hsq
  let τ : TA ⟶ TB :=
    { hom₁ := t, hom₂ := 𝟙 _, hom₃ := inv e,
      comm₁ := ht, comm₂ := hsq, comm₃ := ht₃ }
  have htIso : IsIso t := Pretriangulated.isIso₁_of_isIso₂₃ τ hTA hTB
    (by dsimp [τ]; infer_instance) (by dsimp [τ]; infer_instance)
  let c := finiteCoefficientDirectImageMap φ g ((etaleShriekClosedExceptional A g).obj M)
  let G := R(lowerStar (ModuleCat.{u + 1} B) g)
  let b := etaleShriekClosedCoefficientMap φ g M
  have htε : t ≫ (etaleShriekClosedAdjunction B g).counit.app (F.obj M) =
      F.map ((etaleShriekClosedAdjunction A g).counit.app M) := by
    change F.map ((etaleShriekClosedAdjunction A g).counit.app M) ≫ 𝟙 _ =
      t ≫ (etaleShriekClosedAdjunction B g).counit.app (F.obj M) at ht
    simpa only [Category.comp_id] using ht.symm
  have hpre : G.preimage (inv c ≫ t) = b := by
    apply ((etaleShriekClosedAdjunction B g).homEquiv _ _).symm.injective
    change G.map (G.preimage (inv c ≫ t)) ≫ _ = G.map b ≫ _
    rw [Functor.map_preimage, Category.assoc, htε]
    have hc := closedCoefficient_counit φ g M
    change c ≫ G.map b ≫ _ = _ at hc
    rw [← hc]
    simp
    rfl
  have ht_eq : inv c ≫ t = G.map b := by
    simpa only [Functor.map_preimage] using congrArg G.map hpre
  have : IsIso (G.map b) := by rw [← ht_eq]; infer_instance
  exact isIso_of_reflects_iso b G

/-- Finite quotient coefficient change commutes with ordinary étale locally closed
exceptional restriction and compact support, with the normalized counit identity.
Source: blueprint lemma-change-coefficients-internal-hom--1, proof paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek).

Proof (the twelve steps of the DAG node):
1. The closed subscheme and the two opens are separated finite type over k: use
   lem-weil-pbc-finite-type-over-noetherian, the Noetherian-open lemma and the
   quasi-compact-open finite-type lemma. The coefficient rings are finite and B is
   a finite A-module since it is a quotient (def-weil-l-adic-coefficient-extension).
2. The complementary open has finite cohomological dimension by
   lem-etale-finite-type-sep-closed-derived-dimension. Its higher images are
   constructible by theorem-results-from-etale-theory. A power of l kills A, since
   l is a unit times a positive power of the uniformizer
   (lem-weil-l-adic-extension-integers-dvr). Apply theorem-f-shriek-finite-coefficients--1 to get
   finite-Tor bounded constructibility of Ng in the ambient ordinary adjunction.
3. Exact inverse image preserves constructibility (prop-constructible-pullback).
   Bounded flat models (lemma-flat-models-generators--1), K-flatness of bounded flat complexes,
   and lem-weil-pbc-ringed-topoi-derived-tensor-pullback give the Tor bounds on
   both open restrictions; lem-coef-etale-open-tensor fixes their scalar comparison.
4. The closed-support equivalence proposition-extension-zero-restriction-closed-subscheme--5 lifts
to module sheaves by transporting
   scalar actions. The closed stalk formula and exact conservative geometric stalks
   show that g_* is exact. The inverse-image/direct-image adjunction descends,
   with invertible counit, so derived g_* is fully faithful and reflects isomorphisms.
   On its image, composition with the exceptional counit is a Hom bijection.
5. Apply lemma-change-coefficients-direct-image--1 to Ng and to the complementary-open restriction
   of M. Its counit normalization fixes the comparisons, including the third terms
   of the closed-support triangles.
6. Transpose the complementary-open unit square. The defining coefficient-counit
   equation and the triangle identity identify both transposes with the identity.
7. Apply the exact scalar functor (lem-pur-derived-change-of-rings) to the A-support
   triangle (lemma-local-cohomology-right-adjoint--2). Rotate, use TR3, and rotate back.
   The identity on middle terms and the isomorphism on third terms give an isomorphism
   on first terms (lem-sf-triangle-morphism-iso), whose counit composite is F(epsilon_A).
8. The Hom bijection in step 4 identifies that first map with g_*b_g composed with c_g.
   Reflect invertibility to obtain b_g. Its defining adjunction transpose gives naturality.
9. Apply exact restriction to b_g and the canonical open scalar identification to get b_s.
   Extension by zero preserves bounded constructibility (proposition-six-operations-dctf--6)
   and finite Tor amplitude by lem-coef-etale-open-tensor and its K-flat models.
10. Compose the degreewise open adjunction with the ambient closed adjunction.
    Its counit is g_*(epsilon_j) followed by epsilon_g. Compose c_g with g_*(q_j)
    to obtain q_s, natural and invertible on the specified domain.
11. Expand q_s, b_s and the pasted counit. Naturality of the closed B-counit moves
    j^*b_g past the open counit; the open coefficient-counit identity removes q_j;
    naturality of c_g then reduces the result to the defining transpose of b_g.
12. For S=Z and j the identity, the open adjunction and comparisons identify with
    identities, giving exactly the closed comparison and its counit equation. -/
theorem etaleLocallyClosedShriekComparisons
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ) (hmn : m ≤ n) (hm : 1 ≤ m)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    {Z S : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] :
    @EtaleLocallyClosedShriekComparisons.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) inferInstance inferInstance
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)))
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E m hm))
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)
      (WeilConjectures.finiteTorConstructibleEtale l E n (hm.trans hmn))
      S Z X g inferInstance j
        inferInstance := by
  classical
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E m)
  let φ : A →+* B := Scheme.flatModelReductionCoefficientMap l E m n hmn
  let : Finite A := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn))
  let : Finite B := Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E m hm)
  let : Algebra A B := φ.toAlgebra
  let aX := X ↘ Spec (.of D.k)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian g }
  have : TopologicalSpace.NoetherianSpace S :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := inferInstance
  have : HasCompactification g := (Compactification.ofIsProper g).hasCompactification
  have : HasInvertibleExponent A X :=
    coefficient_hasInvertibleExponent D l _hl E n (hm.trans hmn) X aX
  let ctf := WeilConjectures.finiteTorConstructibleEtale l E n (hm.trans hmn)
  change EtaleLocallyClosedShriekComparisons φ ctf g j
  have hDirect {T : Scheme.{u}} (f : T ⟶ X)
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      (K : DerivedCategoryModule A T) (hK : ctf T K) :
      IsIso (finiteCoefficientDirectImageMap φ f K) := by
    have : LocallyOfFiniteType (f ≫ aX) := inferInstance
    have : QuasiCompact (f ≫ aX) := inferInstance
    let TOver : Over (Spec (.of D.k)) := Over.mk (f ≫ aX)
    let XOver : Over (Spec (.of D.k)) := Over.mk aX
    have : LocallyOfFiniteType TOver.hom := inferInstanceAs (LocallyOfFiniteType (f ≫ aX))
    have : QuasiCompact TOver.hom := inferInstanceAs (QuasiCompact (f ≫ aX))
    have : LocallyOfFiniteType XOver.hom := inferInstanceAs (LocallyOfFiniteType aX)
    have : QuasiCompact XOver.hom := inferInstanceAs (QuasiCompact aX)
    let fOver : TOver ⟶ XOver := Over.homMk f rfl
    have : IsSeparated fOver.left := inferInstanceAs (IsSeparated f)
    have : LocallyOfFiniteType fOver.left := inferInstanceAs (LocallyOfFiniteType f)
    have : QuasiCompact fOver.left := inferInstanceAs (QuasiCompact f)
    exact finiteCoefficientDirectImageMap_isIso D l _hl E n (hm.trans hmn) B
      TOver XOver fOver K hK.1 hK.2
  have hClosed (K : DerivedCategoryModule A X) (hK : ctf X K) :
      ctf Z ((etaleShriekClosedExceptional A g).obj K) :=
    finiteTor_closedExceptional A aX g K hK
  let V : X.Opens := ⟨(Set.range g.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding g).isClosed_range.isOpen_compl⟩
  have hgv : Set.range g.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hIso (K : DerivedCategoryModule A X) (hK : ctf X K) :
      IsIso (etaleShriekClosedCoefficientMap φ g K) := by
    have := hDirect g _ (hClosed K hK)
    have := hDirect V.ι _ (finiteTor_restriction A V.ι K hK)
    exact closedCoefficient_isIso φ g V.ι hgv K
  refine ⟨fun N hN ↦ hDirect g N hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M hM
    have hN := hClosed M hM
    have := hDirect g _ hN
    have := hIso M hM
    have hb : IsIso (etaleShriekLocallyClosedCoefficientMap φ g j M) := by
      dsimp only [etaleShriekLocallyClosedCoefficientMap]
      infer_instance
    exact ⟨hN, finiteTor_restriction A j _ hN, inferInstance, inferInstance, hb,
      locallyClosedCoefficient_counit φ g j M⟩
  · intro P hP
    have := hDirect g _ (finiteTor_extension A j P hP)
    dsimp only [etaleShriekLocallyClosedSupportMap]
    infer_instance
  · intro M N hM hN f
    have := hDirect g _ (hClosed M hM)
    have := hDirect g _ (hClosed N hN)
    exact closedCoefficient_naturality φ g f
  · intro M N hM hN f
    have := hDirect g _ (hClosed M hM)
    have := hDirect g _ (hClosed N hN)
    exact locallyClosedCoefficient_naturality φ g j f
  · intro P Q _ _ f
    exact support_naturality φ g j f
  · intro M
    exact Adjunction.comp_counit_app _ _ M

end AlgebraicGeometry.Etale
