/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

/-! # Transfer of finite-coefficient adjunctions

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
node theorem-f-shriek-finite-coefficients (blueprint: theorem-f-shriek-finite-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.AdjunctionTransfer

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The recorded finite-value etale constructibility intersected with finite Tor amplitude.
Source: blueprint theorem-f-shriek-finite-coefficients, definition of Dctf
(blueprint: theorem-f-shriek-finite-coefficients). -/
abbrev etaleProperty (T : Scheme.{u}) :=
  Etale.DerivedCategory.isBoundedConstructible A T ⊓
    _root_.DerivedCategory.finiteTorAmplitude (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The bounded etale objects included in the bounded-below derived category.
The lower bound is read directly from the recorded constructibility predicate.
Source: blueprint theorem-f-shriek-finite-coefficients, bounded inputs in proof step 1
(blueprint: theorem-f-shriek-finite-coefficients). -/
def etaleToPlus (T : Scheme.{u}) :
    (etaleProperty A T).FullSubcategory ⥤
      _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ObjectProperty.ιOfLE (fun K hK ↦ by
    obtain ⟨a, b, _hab, h⟩ := hK.1.2
    exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ h i (Or.inl hi))⟩)

/-- The finite-coefficient pro-etale convention is etale bounded constructible origin,
intersected with the actual pro-etale Tor test against every degree-zero module sheaf.
Source: blueprint theorem-f-shriek-finite-coefficients and definition-small-pro-etale-site--1
(blueprint: theorem-f-shriek-finite-coefficients). -/
abbrev proEtaleProperty (T : Scheme.{u}) :=
  (Etale.DerivedCategory.isBoundedConstructible A T).map
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⊓
    _root_.DerivedCategory.finiteTorAmplitude
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- Restrict the specified termwise inverse image, retaining its objects and maps.
Source: blueprint theorem-f-shriek-finite-coefficients, comparison equivalences
(blueprint: theorem-f-shriek-finite-coefficients). -/
def comparison (T : Scheme.{u})
    (h : ∀ K, etaleProperty A T K → proEtaleProperty A T
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)) :
    (etaleProperty A T).FullSubcategory ⥤ (proEtaleProperty A T).FullSubcategory :=
  (proEtaleProperty A T).lift
    ((etaleProperty A T).ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory)
    (fun K ↦ h K.obj K.property)

/-- The ordinary etale compactification composite, restricted to Dctf.
Source: blueprint theorem-f-shriek-finite-coefficients, chosen compactification
(blueprint: theorem-f-shriek-finite-coefficients). -/
def etaleLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, etaleProperty A X K → etaleProperty A Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (etaleProperty A X).FullSubcategory ⥤ (etaleProperty A Y).FullSubcategory :=
  (etaleProperty A Y).lift ((etaleProperty A X).ι ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun K ↦ h K.obj K.property)

/-- Inclusion of the generators in their recorded localizing closure.
Source: blueprint theorem-f-shriek-finite-coefficients, Brown restriction
(blueprint: theorem-f-shriek-finite-coefficients). -/
def toLocalizing (T : Scheme.{u}) :
    (proEtaleProperty A T).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A T)).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hgen ↦ hgen K hK)

/-- The compactification functor on the same localizing closures.
Source: blueprint theorem-f-shriek-finite-coefficients, Brown adjunction
(blueprint: theorem-f-shriek-finite-coefficients). -/
def localizingLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K, CategoryTheory.localizingClosure (proEtaleProperty A X) K →
      CategoryTheory.localizingClosure (proEtaleProperty A Y)
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (CategoryTheory.localizingClosure (proEtaleProperty A X)).FullSubcategory ⥤
      (CategoryTheory.localizingClosure (proEtaleProperty A Y)).FullSubcategory :=
  (CategoryTheory.localizingClosure (proEtaleProperty A Y)).lift
    ((CategoryTheory.localizingClosure (proEtaleProperty A X)).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun K ↦ h K.obj K.property)

private theorem boundedConstructible_iff (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨(DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1
      ⟨a, b, ?_, ?_⟩, fun i ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (Or.inl hi))
    · exact (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (Or.inr hi))
  · intro h
    obtain ⟨a, b, ha, hb⟩ :=
      (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 h.1
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (h.2 i),
      min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi

end AlgebraicGeometry.ProEtale.AdjunctionTransfer
