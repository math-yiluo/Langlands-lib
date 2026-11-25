/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Unbounded sections and localization of a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0D6F and its K-injective proof
(blueprint: lem-sfb-unbounded-sections-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.UnboundedSectionsLocalization

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

private lemma compUnit_app
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (X : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app X =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app X
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [Functor.rightDerivedFunctorCompUnit, hi]

/-- Normalization of the derived composition comparison on a K-injective complex.
Source: Stacks Project, Tag 0D6E, the compatibility with resolution units
(blueprint: lem-sfb-unbounded-sections-localization). -/
lemma compIso_objQ
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (I : CochainComplex A ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Q.obj I) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorObjQIso I).hom ≫
        (G.rightDerivedFunctorObjQIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      ((F ⋙ G).rightDerivedFunctorObjQIso I).hom := by
  have h := Functor.rightDerivedNatTrans_app
    (F ⋙ G).rightDerivedFunctor (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)
    ((HomotopyCategory.quotient _ _).obj I)
  simp only [NatTrans.id_app, Category.id_comp] at h
  change (F ⋙ G).rightDerivedFunctorUnit.app _ ≫
    (F.rightDerivedFunctorCompIso G).hom.app _ = _ at h
  rw [compUnit_app] at h
  have hG : IsIso (G.rightDerivedFunctorUnit.app
      ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj I))) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I))))
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, asIso_inv,
    Functor.map_comp, Category.assoc]
  simp only [Iso.app_hom]
  rw [← G.rightDerivedFunctor.map_comp_assoc
    ((DerivedCategory.quotientCompQhIso _).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I))
    ((DerivedCategory.quotientCompQhIso _).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I)),
    Iso.hom_inv_id_app, G.rightDerivedFunctor.map_id, Category.id_comp]
  have hc : (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj I)) ≫
      G.rightDerivedFunctor.map (inv (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj I))) ≫
      inv (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj I))) =
      inv ((F ⋙ G).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj I)) := by
    rw [← cancel_epi ((F ⋙ G).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)), ← Category.assoc, ← Category.assoc, h]
    simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
      Functor.map_id, Category.id_comp]
  have hn := (F.rightDerivedFunctorCompIso G).hom.naturality
    ((DerivedCategory.quotientCompQhIso A).inv.app I)
  change (F ⋙ G).rightDerivedFunctor.map _ ≫ (F.rightDerivedFunctorCompIso G).hom.app _ =
    (F.rightDerivedFunctorCompIso G).hom.app _ ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctor.map _) at hn
  rw [← reassoc_of% hn]
  erw [reassoc_of% hc]
  rfl

/-- The common-universe module category is Grothendieck abelian by the proved
small-site ring-sheaf theorem. Source: Stacks, Section 07A5
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance modulesGrothendieck : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian R

/-- Evaluation at an object, followed by forgetting scalars.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev evaluation (W : C) : ringedSiteModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op W) ⋙
    forget₂ (ModuleCat.{u} (R.obj.obj (op W))) AddCommGrpCat.{u}

/-- Restriction is additive sectionwise.
Source: Stacks, Tags 03DJ and 08FI
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance restrictionAdditive (W : C) : (SheafOfModules.overFunctor.{u} R W).Additive := by
  constructor
  intro M N f g
  ext V x
  rfl

/-- Termwise restriction of an unbounded complex.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev restrictComplex (W : C) :=
  (SheafOfModules.overFunctor.{u} R W).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{u}]

/-- Unbounded derived evaluation, with scalars forgotten after evaluation.
Source: Stacks, Section 07A5 and Tag 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedEvaluation (W : C) :
    DerivedCategory (ringedSiteModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (evaluation R W).rightDerivedFunctor

/-- Unbounded derived restriction. Since sectionwise restriction is exact, its total
right derived functor is the usual termwise restriction on the derived category.
Source: Stacks, Tags 03DJ, 08FI and 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedRestriction (W : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (R.over W))] :
    DerivedCategory (ringedSiteModules.{u} R) ⥤
      DerivedCategory (ringedSiteModules.{u} (R.over W)) :=
  (SheafOfModules.overFunctor.{u} R W).rightDerivedFunctor

end CategoryTheory.UnboundedSectionsLocalization
