/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# A named interface for exact functors on degree-zero objects

The object and morphism functions have their own names. In particular, comparing their
images under a localized functor does not require unfolding the single-degree functor.
The constructions are the canonical Mathlib single functor and its exact-functor comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace SheafExactDegreeZero

variable {V W X : Type*} [Category V] [Category W] [Category X]
  [Abelian V] [Abelian W] [Abelian X]
  [HasDerivedCategory V] [HasDerivedCategory W] [HasDerivedCategory X]

/-- The canonical degree-zero object, kept behind a named object function.
(auxiliary; not a blueprint node) -/
@[irreducible]
def obj (V : Type*) [Category V] [Abelian V] [HasDerivedCategory V] (M : V) :
    DerivedCategory V := (DerivedCategory.singleFunctor V 0).obj M

/-- The canonical degree-zero image of a morphism.
(auxiliary; not a blueprint node) -/
@[irreducible]
def map {M N : V} (f : M ⟶ N) : obj V M ⟶ obj V N := by
  unfold obj
  exact (DerivedCategory.singleFunctor V 0).map f

/-- The degree-zero functor with named object and morphism functions.
(auxiliary; not a blueprint node) -/
def functor (V : Type*) [Category V] [Abelian V] [HasDerivedCategory V] :
    V ⥤ DerivedCategory V where
  obj := obj V
  map := map
  map_id M := by
    unfold map obj
    exact (DerivedCategory.singleFunctor V 0).map_id M
  map_comp f g := by
    unfold map obj
    exact (DerivedCategory.singleFunctor V 0).map_comp f g

/-- The exact-functor comparison for the named degree-zero functor.
(auxiliary; not a blueprint node) -/
def comparison (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    functor V ⋙ F.mapDerivedCategory ≅ F ⋙ functor W := by
  let e := F.mapDerivedCategorySingleFunctor 0
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold functor obj
      exact e.hom.app M
    · unfold functor obj
      exact e.inv.app M
    · unfold functor obj
      exact e.hom_inv_id_app M
    · unfold functor obj
      exact e.inv_hom_id_app M
  · intro M N f
    change F.mapDerivedCategory.map (map f) ≫ _ = _ ≫ map (F.map f)
    unfold map obj
    exact e.hom.naturality f

/-- The canonical derived unit attached to an ordinary morphism into an exact functor.
(auxiliary; not a blueprint node) -/
@[irreducible]
def unit (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : W} {M : V} (η : K ⟶ F.obj M) :
    obj W K ⟶ F.mapDerivedCategory.obj (obj V M) :=
  map η ≫ (comparison F).inv.app M

/-- The named derived unit represents extension to arbitrary unbounded test objects.
(auxiliary; not a blueprint node) -/
def Universal (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : W} {M : V} (η : K ⟶ F.obj M) : Prop :=
  ∀ N : DerivedCategory V,
    Function.Bijective (fun f : obj V M ⟶ N ↦ unit F η ≫ F.mapDerivedCategory.map f)

/-- Degree-zero maps preserve composition.
(auxiliary; not a blueprint node) -/
theorem map_comp {M N P : V} (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map f ≫ map g := by
  unfold map obj
  exact (DerivedCategory.singleFunctor V 0).map_comp f g

/-- Degree-zero maps preserve identities.
(auxiliary; not a blueprint node) -/
theorem map_id (M : V) : map (𝟙 M) = 𝟙 (obj V M) := by
  unfold map obj
  exact (DerivedCategory.singleFunctor V 0).map_id M

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The named universal property is exactly the usual single-functor formula.
The two formulas differ only by associativity of composition.
(auxiliary; not a blueprint node) -/
theorem universal_iff (F : V ⥤ W) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : W} {M : V} (η : K ⟶ F.obj M) :
    Universal F η ↔ ∀ N : DerivedCategory V,
      Function.Bijective (fun f : (DerivedCategory.singleFunctor V 0).obj M ⟶ N ↦
        (DerivedCategory.singleFunctor W 0).map η ≫
          (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫ F.mapDerivedCategory.map f) := by
  unfold Universal unit map comparison functor obj
  change (∀ N : DerivedCategory V,
    Function.Bijective (fun f : (DerivedCategory.singleFunctor V 0).obj M ⟶ N ↦
      ((DerivedCategory.singleFunctor W 0).map η ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫ F.mapDerivedCategory.map f)) ↔ _
  simp only [Category.assoc]

universe u

/-- Sheafification on an essentially small module site, used without searching for an
arbitrary right-adjoint decomposition of the sheaf inclusion.
(auxiliary; not a blueprint node) -/
theorem scalarWeakSheafify {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    (R : Type (u + 1)) [CommRing R] : HasWeakSheafify J (ModuleCat.{u + 1} R) :=
  HasSheafify.isRightAdjoint

/-- The canonical degree-zero sheaf object, with the site's derived-category data fixed once.
(auxiliary; not a blueprint node) -/
def scalarObj {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (R : Type (u + 1)) [CommRing R]
    (M : Sheaf J (ModuleCat.{u + 1} R)) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  obj (Sheaf J (ModuleCat.{u + 1} R)) M

/-- The canonical degree-zero scalar unit, with its restriction functor fixed on a general site.
(auxiliary; not a blueprint node) -/
@[irreducible]
def scalarUnit {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) :
    scalarObj J R F ⟶ (Sheaf.derivedRestrictScalars J φ).obj (scalarObj J S G) :=
  unit (Sheaf.restrictScalars J φ) η

/-- The unbounded universal property of the canonical scalar unit on a general site.
(auxiliary; not a blueprint node) -/
def scalarUniversal {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) : Prop :=
  Sheaf.IsDerivedBaseChange (scalarUnit J φ F G η)

/-- The site specialization retains precisely the original raw single-functor formula.
(auxiliary; not a blueprint node) -/
theorem scalarUniversal_iff {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) :
    scalarUniversal J φ F G η ↔ ∀ N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} S)),
      Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ N ↦
        (DerivedCategory.singleFunctor _ 0).map η ≫
          ((Sheaf.restrictScalars J φ).mapDerivedCategorySingleFunctor 0).inv.app G ≫
            (Sheaf.restrictScalars J φ).mapDerivedCategory.map f) := by
  unfold scalarUniversal scalarUnit scalarObj
  change Universal (Sheaf.restrictScalars J φ) η ↔ _
  exact universal_iff (Sheaf.restrictScalars J φ) η

end SheafExactDegreeZero
