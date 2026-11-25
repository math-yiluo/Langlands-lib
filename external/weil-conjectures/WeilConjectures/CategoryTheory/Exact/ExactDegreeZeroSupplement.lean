/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.ExactDegreeZero

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

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The named interface has the same objects as the usual single functor.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem obj_eq (M : V) : obj V M = (DerivedCategory.singleFunctor V 0).obj M := by
  unfold obj
  rfl

/-- Compatibility with the canonical composition and isomorphism comparisons.
Source: Mathlib exact-functor single comparison and the source library's single coherence.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem comparison_comp (F : V ⥤ W) (G : W ⥤ X) (H : V ⥤ X)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (M : V) :
    (comparison G).inv.app (F.obj M) ≫
      G.mapDerivedCategory.map ((comparison F).inv.app M) ≫
      (Functor.mapDerivedCategoryCompIso F G).hom.app (obj V M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (obj V M) =
    map (e.hom.app M) ≫ (comparison H).inv.app M := by
  unfold comparison functor map obj
  change (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
    (Functor.mapDerivedCategoryCompIso F G).hom.app _ ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app _ =
    (DerivedCategory.singleFunctor X 0).map (e.hom.app M) ≫
      (H.mapDerivedCategorySingleFunctor 0).inv.app M
  rw [← cancel_mono ((H.mapDerivedCategorySingleFunctor 0).hom.app M)]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id]

/-- Units of exact functors respect a specified composition isomorphism.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem unit_comp (F : V ⥤ W) (G : W ⥤ X) (H : V ⥤ X)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H)
    (eD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory)
    (heD : eD = Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e)
    {K : X} {L : W} {M : V}
    (f : K ⟶ G.obj L) (g : L ⟶ F.obj M) (h : K ⟶ H.obj M)
    (hh : h = f ≫ G.map g ≫ e.hom.app M) :
    unit H h = unit G f ≫ G.mapDerivedCategory.map (unit F g) ≫
      eD.hom.app (obj V M) := by
  subst eD
  unfold unit
  subst h
  simp only [map_comp, Functor.map_comp, Category.assoc,
    Iso.trans_hom, NatTrans.comp_app]
  have hn := (comparison G).inv.naturality g
  change map (G.map g) ≫ (comparison G).inv.app (F.obj M) =
    (comparison G).inv.app L ≫ G.mapDerivedCategory.map (map g) at hn
  rw [← reassoc_of% hn, comparison_comp F G H e M]

set_option backward.isDefEq.respectTransparency false in
private theorem derived_id_single {V : Type*} [Category V] [Abelian V]
    [HasDerivedCategory V] (X : V) :
    (Functor.mapDerivedCategoryIdIso V).hom.app ((DerivedCategory.singleFunctor V 0).obj X) =
      ((𝟭 V).mapDerivedCategorySingleFunctor 0).hom.app X := by
  exact Functor.mapDerivedCategoryIdIso_hom_app_singleFunctor_obj X

private theorem raw_unit_id
    {V : Type*} [Category V] [Abelian V] [HasDerivedCategory V]
    (F : V ⥤ V) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 V) (M : V) (f : M ⟶ F.obj M) (hf : f = e.inv.app M) :
    (DerivedCategory.singleFunctor V 0).map f ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app M =
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso V).inv.app
      ((DerivedCategory.singleFunctor V 0).obj M) := by
  rw [← cancel_mono ((Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryIdIso V).hom.app
      ((DerivedCategory.singleFunctor V 0).obj M)), Iso.inv_hom_id_app]
  change ((DerivedCategory.singleFunctor V 0).map f ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app _ ≫
    (Functor.mapDerivedCategoryIdIso V).hom.app _ = _
  rw [derived_id_single]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  simp only [hf, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  change (DerivedCategory.singleFunctor V 0).map (𝟙 M) =
    𝟙 ((DerivedCategory.singleFunctor V 0).obj M)
  exact (DerivedCategory.singleFunctor V 0).map_id M

/-- The named exact unit is normalized by the canonical derived identity comparison.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem unit_id (F : V ⥤ V) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 V) (M : V) (f : M ⟶ F.obj M) (hf : f = e.inv.app M) :
    unit F f =
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso V).inv.app
        (obj V M) := by
  unfold unit map comparison functor obj
  exact raw_unit_id F e M f hf

universe u

end SheafExactDegreeZero
