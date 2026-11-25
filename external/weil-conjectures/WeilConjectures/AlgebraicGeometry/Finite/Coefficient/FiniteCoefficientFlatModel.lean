/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Bounded flat models at finite coefficient levels

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-lem-sf-flat-model`,
`lem-sf-flat-model.md`, all three clauses (blueprint: lemma-flat-models-generators--1).

## Main statements

- `AlgebraicGeometry.Scheme.finiteCoefficient_torAmplitude_iff_flatModel`
- `AlgebraicGeometry.Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel`
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_flatConstructibleModel`
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_boundedFlatConstructibleModel`

The etale encoding uses `ULift` of the same coefficient ring, with its canonical ring
structure; this is the size convention of the recorded etale module-sheaf definitions.
The pro-etale encoding retains site objects in `Type (u + 1)` and morphisms in `Type u`.
No equality between these universes is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048 in
/-- The pro-etale flat-model equivalence at the finite coefficient ring `A_{E,n}`.
Source: blueprint `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`,
conditions (i) and (ii) (blueprint: lemma-flat-models-generators--1).

Proof: work directly in the recorded constant-ring module category, identify site
flatness with categorical flatness, and compare the explicit K-flat tensor model with
the categorical derived tensor. Apply the generic bounded-flat-model theorem, whose
construction chooses a bounded-above flat resolution zero above b. Amplitude tested on
the coefficient sheaf gives exactness
below a. The cokernel of the differential into degree a is flat, since its Tor_1 with
any module is H^(a-1) of the tensor resolution and vanishes by the amplitude bound.
Good truncation at a gives the model. Conversely a bounded complex of flat sheaves is
K-flat and its tensor with a degree-zero sheaf is zero outside the same interval. -/
theorem finiteCoefficient_torAmplitude_iff_flatModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n))
    (_hK : intrinsicFiniteTorsionConstructible l E n hn T K)
    (a b : ℤ) (_hab : a ≤ b) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n) K a b ↔
      ∃ P : CochainComplex (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ,
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
          (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) (P.X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  let A := Padic.coefficientExtensionRing l E n
  let R := proEtaleConstantRing T A
  let C := proEtaleRingModules T R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  have := SheafOfModules.monoidalPreadditive_kfg R
  have := SheafOfModules.isGrothendieckAbelian_kfg R
  have := SheafOfModules.hasFunctorialFlatResolution_kfg R
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let := HasDerivedCategory.standard C
  have := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  have hflat (M : C) : SheafOfModules.IsFlatOnSite (R := R) M ↔
      ObjectProperty.flat M := by
    have e := SheafOfModules.siteSheafTensorRightIso R M
    change exactFunctor _ _ _ ↔ _
    constructor
    · intro h
      have hr := ObjectProperty.prop_of_iso (exactFunctor _ _) e h
      exact ⟨ObjectProperty.prop_of_iso (exactFunctor _ _)
        (BraidedCategory.tensorLeftIsoTensorRight M).symm hr, hr⟩
    · intro h
      exact ObjectProperty.prop_of_iso (exactFunctor _ _) e.symm h.2
  -- Fix the complex tensor structure before comparing the two K-flat predicates.
  let : MonoidalCategory (CochainComplex C ℤ) :=
    HomologicalComplex.monoidalCategory C (.up ℤ)
  have hk (P : CochainComplex C ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    apply (HomotopyCategory.kFlat_quotient_obj_iff P).mp
    apply (HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)).mpr
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        (MonoidalCategory.tensorObj ((HomotopyCategory.quotient C (.up ℤ)).obj N)
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := by
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hright, hright⟩
  have heq (L P : CochainComplex C ℤ) (e : DerivedCategory.Q.obj L ≅ K)
      (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) (M : C) :
      Nonempty (MonoidalCategory.tensorObj K ((DerivedCategory.singleFunctor C 0).obj M) ≅
        derivedTensor T A L ((HomologicalComplex.single C (.up ℤ) 0).obj M) P f hf hP) := by
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
    exact ⟨(MonoidalCategory.tensorIso (e.symm ≪≫ (asIso (DerivedCategory.Q.map f)).symm)
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)) ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P _ (hk P hP)⟩
  have hamp : HasProEtaleTorAmplitude T A K a b ↔
      DerivedCategory.torAmplitudeIn C a b K := by
    constructor
    · intro h M
      have : (DerivedCategory.Q (C := C)).EssSurj :=
        Localization.essSurj _ (HomologicalComplex.quasiIso _ (.up ℤ))
      let L := (DerivedCategory.Q (C := C)).objPreimage K
      let e := (DerivedCategory.Q (C := C)).objObjPreimageIso K
      obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
      obtain ⟨eq⟩ := heq L P e f hf hP M
      rw [DerivedCategory.homologyConcentratedIn_iff]
      refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
      · intro i hi
        exact (h.2 L P ⟨e⟩ f hf hP M i (.inl hi)).of_iso
          ((DerivedCategory.homologyFunctor C i).mapIso eq)
      · intro i hi
        exact (h.2 L P ⟨e⟩ f hf hP M i (.inr hi)).of_iso
          ((DerivedCategory.homologyFunctor C i).mapIso eq)
    · intro h
      refine ⟨_hab, ?_⟩
      rintro L P ⟨e⟩ f hf hP M i hi
      obtain ⟨eq⟩ := heq L P e f hf hP M
      have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj
          (MonoidalCategory.tensorObj K ((DerivedCategory.singleFunctor C 0).obj M))) := by
        obtain ⟨hge, hle⟩ := (DerivedCategory.homologyConcentratedIn_iff _ _ _).1 (h M)
        rcases hi with hi | hi
        · exact (DerivedCategory.isGE_iff _ a).1 hge i hi
        · exact (DerivedCategory.isLE_iff _ b).1 hle i hi
      exact hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso eq.symm)
  rw [hamp]
  constructor
  · intro h
    obtain ⟨P, hge, hle, hf, ⟨e⟩⟩ :=
      (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).1 h
    refine ⟨P, fun q ↦ (hflat _).2 (hf q), ?_, ⟨e.symm⟩⟩
    intro q hq
    rcases hq with hq | hq
    · exact P.isZero_of_isStrictlyGE a q hq
    · exact P.isZero_of_isStrictlyLE b q hq
  · rintro ⟨P, hf, hz, ⟨e⟩⟩
    exact (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).2
      ⟨P, (P.isStrictlyGE_iff a).2 (fun q hq ↦ hz q (.inl hq)),
        (P.isStrictlyLE_iff b).2 (fun q hq ↦ hz q (.inr hq)),
        fun q ↦ (hflat _).1 (hf q), ⟨e.symm⟩⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The same equivalence on the small etale site, with finite-value constructibility.
Source: blueprint `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`,
the small-etale clause (blueprint: lemma-flat-models-generators--1).

Proof: convert bounded constructibility using the constructible-sheaf comparison and
apply lem-sf-etale-flat-model. The flat terms and support interval are unchanged. -/
theorem finiteCoefficient_hasTorAmplitude_iff_flatModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K)
    (a b : ℤ) (_hab : a ≤ b) :
    DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T a b K ↔
      ∃ P : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) ℤ,
        IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  have : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    Equiv.ulift.finite_iff.mpr inferInstance
  have hK' : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T K := by
    obtain ⟨c, d, -, hcd⟩ := _hK.2
    refine ⟨⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩, fun q ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hcd q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hcd q (.inr hq)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (_hK.1 q)
  exact hasTorAmplitudeIn_iff_exists_flatModel _ a b _hab K hK'

end AlgebraicGeometry.Etale
