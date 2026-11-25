/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
/-! # Ext naturality for a square of exact functors

Source: Stacks Project, Section 01F7, functoriality of derived inverse image.
-/
@[expose] public section
set_option autoImplicit false
universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Abelian.Ext

/-- The composition comparison with independent Ext universes.
Source: Stacks Project, Tag 015F. Adapted from the complete proof of
`exactFunctorCompositionComparison` in Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison.
Identify Ext classes with derived morphisms, verify the single-complex comparison
degreewise, and apply shifted naturality. Each Ext universe can be chosen independently. -/
private theorem compositionComparison
    {C : Type u₁} {D : Type u₂} {E : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₄} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₄} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) {X Y : C} {n : ℕ} (x : Ext.{w₁} X Y n) :
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
      repeat' conv =>
        pattern (occs := *) (Functor.mapDerivedCategorySingleFunctor _ 0).hom.app _
        simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
          DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
          Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
          Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
          NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
          Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
        erw [Category.id_comp]
        dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
      rw [Functor.map_comp]
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

/-- A natural isomorphism between composite exact functors intertwines their Ext maps.
Source: Stacks Project, Section 01F7; naturality of maps in derived categories.
(blueprint: lem-pc-ext-exact-functor-square)

Proof: Apply each exact functor termwise to complexes. The natural isomorphism c
then induces a chain isomorphism between the two resulting composite functors.
Its naturality holds for chain maps and hence for roofs representing morphisms
in the derived category, since its components are isomorphisms. It commutes with
shifts termwise. A degree-n Ext class is a derived morphism from the single
complex of A to the n-shift of the single complex of F. Naturality for that
morphism gives exactly the equality below, after identifying the single-complex
comparisons for composite functors. Shrinking these morphism sets in HasExt
preserves the equality. This works in degree zero and in all higher degrees;
zero objects or zero classes require no separate nonvanishing hypothesis.
-/
theorem mapExactFunctor_square
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{w₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{w₃} C₃]
    {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasExt.{w₄} C₄]
    (G : C₁ ⥤ C₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (J : C₁ ⥤ C₃) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (J' : C₂ ⥤ C₄) [J'.Additive] [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (GW : C₃ ⥤ C₄) [GW.Additive] [PreservesFiniteLimits GW] [PreservesFiniteColimits GW]
    (c : G ⋙ J' ≅ J ⋙ GW) {A F : C₁} (n : ℕ) (x : Ext A F n) :
    ((x.mapExactFunctor G).mapExactFunctor J').comp (Ext.mk₀ (c.app F).hom)
        (add_zero n) =
      (Ext.mk₀ (c.app A).hom).comp ((x.mapExactFunctor J).mapExactFunctor GW)
        (zero_add n) := by
  let := comp_preservesFiniteLimits G J'
  let := comp_preservesFiniteColimits G J'
  have hcomp := compositionComparison G J' (G ⋙ J') (Iso.refl _) x
  have hsquare := compositionComparison J GW (G ⋙ J') c x
  have heq : x.mapExactFunctor (G ⋙ J') = (x.mapExactFunctor G).mapExactFunctor J' := by
    simpa using hcomp
  rw [heq] at hsquare
  exact hsquare

end CategoryTheory.Abelian.Ext
