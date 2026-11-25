/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyModel
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # The ordinary degree-zero structure class

Source: Stacks Project, Tag 06Z0.
(blueprint: lem-sc-open-sections-ordinary-structure-class).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true in
private theorem mapHomologyIso_homologyπ
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    (F : V ⥤ W) [F.Additive] [F.PreservesHomology] (S : ShortComplex V) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [ShortComplex.LeftHomologyData.mapCyclesIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change _ ≫ F.map S.leftHomologyData.π ≫ F.map S.leftHomologyData.homologyIso.inv = _
  rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  simp only [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
private theorem single_map_homology
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    (F : V ⥤ W) [F.Additive] [F.PreservesHomology] (M : V) :
    ((((HomologicalComplex.single V (.up ℤ) 0).obj M).sc 0).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M).hom =
      HomologicalComplex.homologyMap
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).hom := by
  let K := (HomologicalComplex.single V (.up ℤ) 0).obj M
  let α := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M
  rw [← cancel_epi (((F.mapHomologicalComplex (.up ℤ)).obj K).homologyπ 0)]
  change ((K.sc 0).map F).homologyπ ≫ _ = _
  rw [← Category.assoc, mapHomologyIso_homologyπ]
  dsimp only [K, Functor.comp_obj]
  simp only [Category.assoc]
  rw [← F.map_comp]
  change _ ≫ F.map
      (((HomologicalComplex.single V (.up ℤ) 0).obj M).homologyπ 0 ≫ _) = _
  simp only [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.homologyπ_naturality_assoc]
  simp only [HomologicalComplex.singleObjCyclesSelfIso_hom, F.map_comp]
  have hc : ((K.sc 0).mapCyclesIso F).hom ≫ F.map (K.iCycles 0) =
      ((F.mapHomologicalComplex (.up ℤ)).obj K).iCycles 0 :=
    ShortComplex.mapCyclesIso_hom_iCycles (K.sc 0) F
  rw [← Category.assoc, hc]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem extension_single_homology (A : Type u) [CommRing A] :
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of A A) 0 0 rfl
    K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of A A) =
      (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso e ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A A) := by
  intro K e
  apply Iso.ext
  change (K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of A A)).hom =
    HomologicalComplex.homologyMap e.hom 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A A)).hom
  rw [← cancel_epi ((K.extend ComplexShape.embeddingDownNat).homologyπ 0)]
  dsimp only [K, ChainComplex.single₀] at *
  simp only [HomologicalComplex.homologyπ_extendHomologyIso_hom_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.homologyπ_naturality_assoc]
  simp only [HomologicalComplex.singleObjCyclesSelfIso_hom]
  rw [← Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  simp only [e, HomologicalComplex.extendSingleIso_hom_f, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
private theorem single_homology_map
    {V : Type*} [Category V] [Abelian V] {M N : V}
    (f : (HomologicalComplex.single V (.up ℤ) 0).obj M ⟶
      (HomologicalComplex.single V (.up ℤ) 0).obj N) :
    HomologicalComplex.homologyMap f 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 N).hom =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ f.f 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom := by
  let g := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ f.f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom
  have hf : f = (HomologicalComplex.single V (.up ℤ) 0).map g := by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0
    · subst n
      simp [g, HomologicalComplex.single_map_f_self]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _
  conv_lhs => rw [hf, HomologicalComplex.singleObjHomologySelfIso_hom_naturality]

set_option backward.defeqAttrib.useBackward true in
private theorem normalized_homology_map
    {V : Type*} [Category V] [Abelian V]
    {X Y : CochainComplex V ℤ} {M N : V}
    (a : X ≅ (HomologicalComplex.single V (.up ℤ) 0).obj M)
    (b : Y ≅ (HomologicalComplex.single V (.up ℤ) 0).obj N) (f : X ⟶ Y) :
    HomologicalComplex.homologyMap f 0 ≫
        ((HomologicalComplex.homologyFunctor V (.up ℤ) 0).mapIso b ≪≫
          HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 N).hom =
      ((HomologicalComplex.homologyFunctor V (.up ℤ) 0).mapIso a ≪≫
          HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M).hom ≫
        ((HomologicalComplex.eval V (.up ℤ) 0).mapIso a ≪≫
          HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ f.f 0 ≫
        ((HomologicalComplex.eval V (.up ℤ) 0).mapIso b ≪≫
          HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom := by
  have h := single_homology_map (a.inv ≫ f ≫ b.hom)
  have h' := congrArg
    (fun t ↦ HomologicalComplex.homologyMap a.hom 0 ≫ t) h
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc] at h'
  rw [← HomologicalComplex.homologyMap_comp_assoc, Iso.hom_inv_id,
    HomologicalComplex.homologyMap_id, Category.id_comp] at h'
  simpa only [HomologicalComplex.comp_f, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.eval_map, Category.assoc] using h'

set_option backward.defeqAttrib.useBackward true in
private theorem map_normalized_homology
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    (F : V ⥤ W) [F.Additive] [F.PreservesHomology]
    {X : CochainComplex V ℤ} {M : V}
    (a : X ≅ (HomologicalComplex.single V (.up ℤ) 0).obj M) :
    ((X.sc 0).mapHomologyIso F).hom ≫
        F.map (((HomologicalComplex.homologyFunctor V (.up ℤ) 0).mapIso a ≪≫
          HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M).hom) =
      ((HomologicalComplex.homologyFunctor W (.up ℤ) 0).mapIso
        ((F.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
            HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).hom := by
  have hn : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map a.hom) 0 ≫
        ((((HomologicalComplex.single V (.up ℤ) 0).obj M).sc 0).mapHomologyIso F).hom =
      ((X.sc 0).mapHomologyIso F).hom ≫ F.map
        (HomologicalComplex.homologyMap a.hom 0) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor V (.up ℤ) 0).map a.hom) F
  change ((X.sc 0).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap a.hom 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M).hom) =
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map a.hom ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).hom
  rw [F.map_comp, ← Category.assoc, ← hn, Category.assoc,
    single_map_homology, HomologicalComplex.homologyMap_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
private theorem map_single_degree_hom
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    (F : V ⥤ W) [F.Additive] {X : CochainComplex V ℤ} {M : V}
    (a : X ≅ (HomologicalComplex.single V (.up ℤ) 0).obj M) :
    ((HomologicalComplex.eval W (.up ℤ) 0).mapIso
      ((F.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
          HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj M)).hom =
      F.map (((HomologicalComplex.eval V (.up ℤ) 0).mapIso a ≪≫
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.eval_map,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.map_comp, Category.assoc]
  change F.map (a.hom.f 0) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj M)).hom = _
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
private theorem map_single_degree_inv
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    (F : V ⥤ W) [F.Additive] {X : CochainComplex V ℤ} {M : V}
    (a : X ≅ (HomologicalComplex.single V (.up ℤ) 0).obj M) :
    ((HomologicalComplex.eval W (.up ℤ) 0).mapIso
      ((F.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
          HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj M)).inv =
      F.map (((HomologicalComplex.eval V (.up ℤ) 0).mapIso a ≪≫
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv) := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, HomologicalComplex.eval_map,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.map_comp]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj M)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M).f 0 ≫
        F.map (a.inv.f 0) = _
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  rw [← Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
private theorem normalized_forget_comparison
    {R S : Type u} [Ring R] [Ring S]
    {X : CochainComplex (ModuleCat.{u} R) ℤ}
    {Y : CochainComplex (ModuleCat.{u} S) ℤ}
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (a : X ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj M)
    (b : Y ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj N)
    (z : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj X ≅
      ((forget₂ (ModuleCat.{u} S) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj Y) :
    let P := forget₂ (ModuleCat.{u} R) AddCommGrpCat
    let Q := forget₂ (ModuleCat.{u} S) AddCommGrpCat
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
    let aH := (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso a ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M
    let bH := (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso b ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 N
    let a₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso a ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
    let b₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso b ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 N
    (((X.sc 0).mapHomologyIso P).symm ≪≫ H.mapIso z ≪≫
        (Y.sc 0).mapHomologyIso Q).hom ≫ Q.map bH.hom =
      P.map aH.hom ≫ P.map a₀.inv ≫ z.hom.f 0 ≫ Q.map b₀.hom := by
  intro P Q H aH bH a₀ b₀
  let a' := (P.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
    (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app M
  let b' := (Q.mapHomologicalComplex (.up ℤ)).mapIso b ≪≫
    (HomologicalComplex.singleMapHomologicalComplex Q (.up ℤ) 0).app N
  have ha := map_normalized_homology P a
  have hb := map_normalized_homology Q b
  have hz := normalized_homology_map a' b' z.hom
  change ((X.sc 0).mapHomologyIso P).inv ≫
    HomologicalComplex.homologyMap z.hom 0 ≫ ((Y.sc 0).mapHomologyIso Q).hom ≫
      Q.map bH.hom = _
  rw [hb, hz, ← ha, map_single_degree_inv, map_single_degree_hom]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

private theorem normalized_forget_comparison_apply
    {R S : Type u} [Ring R] [Ring S]
    {X : CochainComplex (ModuleCat.{u} R) ℤ}
    {Y Z : CochainComplex (ModuleCat.{u} S) ℤ}
    {M : ModuleCat.{u} R} {N E : ModuleCat.{u} S}
    (a : X ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj M)
    (b : Y ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj N)
    (c : Z ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj E)
    (z : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj X ≅
      ((forget₂ (ModuleCat.{u} S) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj Y)
    (f : Z ⟶ Y) (x : M) (y : E) :
    let P := forget₂ (ModuleCat.{u} R) AddCommGrpCat
    let Q := forget₂ (ModuleCat.{u} S) AddCommGrpCat
    let aH := (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso a ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M
    let cH := (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso c ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 E
    let a₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso a ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
    let c₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso c ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 E
    let i := ((X.sc 0).mapHomologyIso P).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).mapIso z ≪≫
      (Y.sc 0).mapHomologyIso Q
    z.hom.f 0 (a₀.inv x) = f.f 0 (c₀.inv y) →
      aH.inv x = i.inv (HomologicalComplex.homologyMap f 0 (cH.inv y)) := by
  intro P Q aH cH a₀ c₀ i h
  let bH := (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso b ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 N
  let b₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso b ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 N
  have hcmp : i.hom ≫ Q.map bH.hom =
      P.map aH.hom ≫ P.map a₀.inv ≫ z.hom.f 0 ≫ Q.map b₀.hom :=
    normalized_forget_comparison a b z
  have hf : HomologicalComplex.homologyMap f 0 ≫ bH.hom =
      cH.hom ≫ c₀.inv ≫ f.f 0 ≫ b₀.hom :=
    normalized_homology_map c b f
  apply (ConcreteCategory.bijective_of_isIso (i.hom ≫ Q.map bH.hom)).1
  conv_lhs => rw [hcmp]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change b₀.hom (z.hom.f 0 (a₀.inv (aH.hom (aH.inv x)))) =
    (HomologicalComplex.homologyMap f 0 ≫ bH.hom) (cH.inv y)
  rw [Iso.inv_hom_id_apply, hf]
  simp only [ConcreteCategory.comp_apply]
  have hc : cH.hom (cH.inv y) = y :=
    congrArg (fun k : E ⟶ E ↦ k.hom y) cH.inv_hom_id
  erw [hc]
  exact congrArg b₀.hom h

private theorem mapped_single_homology_inv
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    (F : V ⥤ W) [F.Additive] {X : CochainComplex V ℤ} {M : V}
    (e : X ≅ (HomologicalComplex.single V (.up ℤ) 0).obj M) :
    let H := HomologicalComplex.homologyFunctor W (.up ℤ) 0
    let s := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M
    (H.mapIso ((F.mapHomologicalComplex (.up ℤ)).mapIso e ≪≫ s) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv =
      (H.mapIso s ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
          HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map e.inv) 0 := by
  intro H s
  simp only [Functor.mapIso_trans, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem ordinary_section_one (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) :
    let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
    let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
    let O := SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)
    (openComparisonSectionsIso A U).hom.app O
      ((S.map (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U
        (moduleRings (Spec (.of A)).toRingedSpace)).inv) (1 : B)) =
      tilde.toOpen (ModuleCat.of A A) U (1 : A) := by
  intro B S O
  simp only [TopologicalSpace.Opens.sheafOfModulesEquivOverUnit, Iso.refl_inv]
  change (openComparisonSectionsIso A U).hom.app O (1 : B) = _
  unfold openComparisonSectionsIso
  dsimp
  change (Spec (.of A)).presheaf.map
    (eqToHom (by simp : U = U.ι ''ᵁ ⊤)).op (1 : _) = _
  rw [map_one]
  change (1 : _) = StructureSheaf.const (1 : A) (1 : A) U (by simp)
  exact (StructureSheaf.const_one U).symm


set_option backward.defeqAttrib.useBackward true in
private theorem section_iso_one (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens)
    {M : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)}
    (g : SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace) ⟶ M) :
    let T := openComparisonRestriction A U
    let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
    let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
    let P := forget₂ (ModuleCat.{u} B) AddCommGrpCat
    let Q := forget₂ (ModuleCat.{u} A) AddCommGrpCat
    (P.map (S.map (T.map g)) ≫ (openComparisonSectionsIso A U).hom.app M) (1 : B) =
      (Q.map ((affineOpenSections A U).map g))
        (tilde.toOpen (ModuleCat.of A A) U (1 : A)) := by
  intro T S B P Q
  have hn : P.map (S.map (T.map g)) ≫ (openComparisonSectionsIso A U).hom.app M =
      (openComparisonSectionsIso A U).hom.app
        (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) ≫
          Q.map ((affineOpenSections A U).map g) :=
    (openComparisonSectionsIso A U).hom.naturality g
  have hn' := ConcreteCategory.congr_hom hn (1 : B)
  change (ConcreteCategory.hom (P.map (S.map (T.map g)) ≫
    (openComparisonSectionsIso A U).hom.app M)) (1 : B) = _
  rw [hn']
  simp only [ConcreteCategory.comp_apply]
  have h := ordinary_section_one A U
  change (openComparisonSectionsIso A U).hom.app
    (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) (1 : B) =
      tilde.toOpen (ModuleCat.of A A) U (1 : A) at h
  exact congrArg (Q.map ((affineOpenSections A U).map g)) h


set_option backward.defeqAttrib.useBackward true in
/-- The restricted ordinary class of one agrees with the tilde/sections unit class.
Source: Stacks Project, Tag 06Z0, the tilde/sections unit, and its restriction to U.
(blueprint: lem-sc-open-sections-ordinary-structure-class).

Proof: Use the extension comparison to identify L with A[0]. The extension homology
isomorphism followed by the single homology isomorphism sends its degree-zero cycle
one to one. The tilde single comparison is identity in degree zero. Under tildeSelf,
tilde.toOpen sends one to the constant structure section one, by toOpen_eq_const and
StructureSheaf.const_one. Restricting the unit sheaf and the over-site equivalence
preserve this section: their degree-zero maps are restriction of the structure ring,
hence preserve one. The restriction/sections isomorphism is restrictAppIso at the top
followed by transport along U = image(top); these are the same section on U. Apply
homology to these degree-zero maps. Naturality of homologyπ gives equality of the
cycle classes. Finally conjugate by the two exact scalar-forgetting homology
isomorphisms in openComparisonOrdinaryIso; their naturality identifies the same
cycles in the additive-group category. All complexes are concentrated in degree zero,
so there are no boundaries. For empty U and the zero ring every section is zero and
the identical calculation holds. No derived unit or comparison equivalence is used.
-/
theorem openComparison_ordinary_structure_class (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) :
    let T := openComparisonRestriction A U
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    let L := K.extend ComplexShape.embeddingDownNat
    let C := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj L
    let η₀ : 𝟭 (ModuleCat.{u} A) ⟶ koszulOpenTilde A ⋙ affineOpenSections A U :=
      { app := fun M ↦ tilde.toOpen M U
        naturality := fun _ _ g ↦ (tilde.toOpen_map_app g U).symm }
    let η := (NatTrans.mapHomologicalComplex η₀ (.up ℤ)).app L
    let j : L.homology 0 ≅ ModuleCat.of A A :=
      K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of A A)
    let e₀ : L ≅ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A) :=
      HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of A A) 0 0 rfl
    let e₁ : C ≅ (CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) :=
      ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).mapIso e₀ ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (koszulOpenTilde A) (.up ℤ) 0).app
        (ModuleCat.of A A)
    let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
    let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
    let D := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace))
    let J := (T.mapHomologicalComplex (.up ℤ)).obj C
    let e : J ≅ D :=
      (T.mapHomologicalComplex (.up ℤ)).mapIso e₁ ≪≫
        (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app
          (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) ≪≫
        (CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).mapIso
            (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U
              (moduleRings (Spec (.of A)).toRingedSpace))
    let ε : ((S.mapHomologicalComplex (.up ℤ)).obj D).homology 0 ≅ ModuleCat.of B B :=
      (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app _) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of B B)
    HomologicalComplex.homologyMap
        ((S.mapHomologicalComplex (.up ℤ)).map e.inv) 0 (ε.inv (1 : B)) =
      (openComparisonOrdinaryIso A U C).inv
        ((HomologicalComplex.homologyMap η 0) (j.inv (1 : A))) := by
  intro T K L C η₀ η j e₀ e₁ B S D J e ε
  let O := SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)
  let X := (S.mapHomologicalComplex (.up ℤ)).obj J
  let Y := ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj C
  let a : X ≅ (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj
      (ModuleCat.of B B) := (S.mapHomologicalComplex (.up ℤ)).mapIso e ≪≫
    (HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app
      (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace))
  let b : Y ≅ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      ((affineOpenSections A U).obj O) :=
    ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).mapIso e₁ ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (affineOpenSections A U) (.up ℤ) 0).app O
  let a₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso a ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of B B)
  let l₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso e₀ ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)
  let z := (NatIso.mapHomologicalComplex (openComparisonSectionsIso A U) (.up ℤ)).app C
  have hdegree : z.hom.f 0 (a₀.inv (1 : B)) = η.f 0 (l₀.inv (1 : A)) := by
    have he : a₀.inv = S.map (T.map (e₁.inv.f 0)) := by rfl
    have hl : l₀.inv = e₀.inv.f 0 := by rfl
    have he₁ : e₁.inv.f 0 = (koszulOpenTilde A).map (e₀.inv.f 0) := by rfl
    have hs : z.hom.f 0 (a₀.inv (1 : B)) =
        ((affineOpenSections A U).map (e₁.inv.f 0))
          (tilde.toOpen (ModuleCat.of A A) U (1 : A)) := by
      have hh := section_iso_one A U (e₁.inv.f 0)
      rw [he]
      exact hh
    have hn := ConcreteCategory.congr_hom
      (tilde.toOpen_map_app (e₀.inv.f 0) U) (1 : A)
    rw [hs, he₁, hl]
    exact hn
  have h := normalized_forget_comparison_apply (R := B) (S := A)
    (X := X) (Y := Y) (Z := L) (M := ModuleCat.of B B)
    (N := (affineOpenSections A U).obj O) (E := ModuleCat.of A A)
    a b e₀ z η (1 : B) (1 : A) hdegree
  have hj : j = (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso e₀ ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A A) :=
    extension_single_homology A
  have ha : ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).mapIso a ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of B B)).inv =
        ε.inv ≫ HomologicalComplex.homologyMap
          ((S.mapHomologicalComplex (.up ℤ)).map e.inv) 0 :=
    mapped_single_homology_inv S e
  erw [ha, ← hj] at h
  exact h

end
end AlgebraicGeometry
