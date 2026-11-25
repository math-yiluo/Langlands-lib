/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-!
# Ext composition comparison

Source: Stacks Project, derived.tex, Tag 015F; Mathlib Ext.Map.
(blueprint: lem-weil-pbc-ext-exact-functor-composition-comparison)
-/

@[expose] public section

universe w w' w''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

private lemma singleComparison_hom {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] (a : A) :
    (T.mapDerivedCategorySingleFunctor 0).hom.app a =
      T.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj a) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).hom.app a) := by
  simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
    Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
  erw [Category.id_comp]
/-- Exact functors respect composition after transport by a natural isomorphism.
The Ext universes of the three categories may be chosen independently.
The comparison is established on localized single complexes and then shifted.
Source: Stacks Project, derived.tex, Tag 015F (lemma-right-derived-exact-functor:
every complex computes an exact functor), and Mathlib Ext.Map's definition through
localized shifted morphisms.

Proof: identify Ext with shifted morphisms between complexes concentrated in degree zero.
The induced functor for F followed by G agrees with that for their composite, through
its canonical comparison. The natural isomorphism e induces an isomorphism on complexes
and their localization. Its naturality for the shifted morphism representing x says
that mapping x by H and then e at Y equals e at X followed by mapping x by F then G.
The degree-zero components are precisely Ext.mk₀ of e.hom.app. The comparison with
single complexes and the shift isomorphisms cancel on both sides, giving the equality.
(blueprint: lem-weil-pbc-ext-exact-functor-composition-comparison)
-/
theorem mapExactFunctor_comp_mk₀_eq_sheaf
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor H).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp
        ((x.mapExactFunctor F).mapExactFunctor G) (zero_add n) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard E
  set_option backward.isDefEq.respectTransparency false in
    let := comp_preservesFiniteLimits F G
    let := comp_preservesFiniteColimits F G
    have hc (A : C) :
        (Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
            ((DerivedCategory.singleFunctor C 0).obj A) ≫
          G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app A) ≫
          (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj A) =
        (H.mapDerivedCategorySingleFunctor 0).hom.app A ≫
          (DerivedCategory.singleFunctor E 0).map (e.hom.app A) := by
      rw [singleComparison_hom F, singleComparison_hom G, singleComparison_hom H,
        Functor.map_comp]
      simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
      simp only [← DerivedCategory.Q_obj_single_obj] at *
      erw [G.mapDerivedCategoryFactors.hom.naturality_assoc]
      have hf := Functor.mapDerivedCategoryCompIso_fac F G
        ((HomologicalComplex.single C (.up ℤ) 0).obj A)
      have he := Functor.mapDerivedCategoryNatIso_fac e
        ((HomologicalComplex.single C (.up ℤ) 0).obj A)
      simp only [Functor.comp_obj] at hf he
      have hm :
          (G.mapHomologicalComplex (.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app A) ≫
            (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj A) =
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app
              ((HomologicalComplex.single C (.up ℤ) 0).obj A) ≫
            (HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (.up ℤ) 0).hom.app A := by
        ext i
        by_cases hi : i = 0
        · subst i
          simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
        · simp [HomologicalComplex.singleMapHomologicalComplex, hi]
      simp only [Functor.comp_map]
      rw [← DerivedCategory.Q.map_comp, hm, DerivedCategory.Q.map_comp]
      erw [reassoc_of% hf, reassoc_of% he]
      rw [← DerivedCategory.Q.map_comp]
      have hn :
          (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
              ((HomologicalComplex.single C (.up ℤ) 0).obj A) ≫
            (HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (.up ℤ) 0).hom.app A =
          (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app A ≫
            (HomologicalComplex.single E (.up ℤ) 0).map (e.hom.app A) := by
        ext i
        by_cases hi : i = 0
        · subst i
          simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
        · simp [HomologicalComplex.singleMapHomologicalComplex, hi]
      rw [hn, DerivedCategory.Q.map_comp]
      rfl
    ext
    simp only [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom]
    have : NatTrans.CommShift
        (Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso F G).symm).hom ℤ := by
      dsimp only [Iso.trans_hom]
      infer_instance
    have hi (A : C) :
        (H.mapDerivedCategorySingleFunctor 0).inv.app A ≫
          (Functor.mapDerivedCategoryNatIso e ≪≫
            (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
            ((DerivedCategory.singleFunctor C 0).obj A) =
        (DerivedCategory.singleFunctor E 0).map (e.hom.app A) ≫
          (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj A) ≫
          G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app A) := by
      rw [← cancel_mono (G.mapDerivedCategory.map
        ((F.mapDerivedCategorySingleFunctor 0).hom.app A) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj A))]
      simp only [Category.assoc]
      rw [hc A, Iso.inv_hom_id_app_assoc,
        ← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
      erw [G.mapDerivedCategory.map_id]
      simp only [Category.id_comp, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have h := ShiftedHom.map_naturality x.hom
      (Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom
    simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
      ShiftedHom.map, Functor.map_comp, Category.assoc] at h ⊢
    have hh := congrArg (fun t ↦ (H.mapDerivedCategorySingleFunctor 0).inv.app X ≫ t ≫
        (G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
          (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj Y))⟦(n : ℤ)⟧') h
    simp only [Category.assoc, ← Functor.map_comp, hc] at hh
    rw [reassoc_of% (hi X)] at hh
    simp only [Functor.map_comp, Functor.comp_map, Functor.commShiftIso_comp_hom_app,
      Category.assoc] at hh
    simp only [← Functor.commShiftIso_hom_naturality_assoc] at hh
    exact hh

end CategoryTheory.Abelian.Ext
