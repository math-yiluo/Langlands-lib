/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernTargetNormalization
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernRootNormalizationEquation

/-! # Inverse image of the normalized Kummer transpose

Source: classes (2) (blueprint: lem-sp-tower-kummer-pullback-transpose).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local implicit_reducible] HomotopyCategory.singleFunctors

section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
private theorem square_factors (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [CategoryTheory.Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors,
    CategoryTheory.Functor.mapDerivedCategoryNatIso_fac]
  rw [← CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors F G K]
  erw [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact Category.assoc _ _ _

private theorem single_factors (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : A) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj X) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) := by
  erw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X]
  erw [Iso.hom_inv_id_app_assoc]

private theorem square_single (e : F ⋙ G ≅ H ⋙ I) (X : A) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        ((DerivedCategory.singleFunctor A 0).obj X) ≫
      I.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (H.obj X) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj X
  let cF := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let cG := HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0
  let cH := HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0
  let cI := HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have hc : ec.hom.app K ≫ (I.mapHomologicalComplex (.up ℤ)).map (cH.hom.app X) ≫
      cI.hom.app (H.obj X) =
      (G.mapHomologicalComplex (.up ℤ)).map (cF.hom.app X) ≫ cG.hom.app (F.obj X) ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X) := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        ec, NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.single_map_f_self, cF, cG, cH, cI,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        CategoryTheory.Functor.map_comp, Category.assoc]
      simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc]
      simpa only [K, CategoryTheory.Functor.comp_map, Category.assoc] using!
        congrArg (fun z ↦ z ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((H ⋙ I).obj X)).inv)
          (e.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).symm
    · exact ((F ⋙ G).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi)).eq_of_src _ _
  rw [single_factors H X, single_factors I (H.obj X), single_factors F X,
    single_factors G (F.obj X)]
  change (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map
        (H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (cH.hom.app X)) ≫
      (I.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj (H.obj X)) ≫
        DerivedCategory.Q.map (cI.hom.app (H.obj X))) =
    G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (cF.hom.app X)) ≫
      (G.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj X)) ≫
        DerivedCategory.Q.map (cG.hom.app (F.obj X))) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X))
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [I.mapDerivedCategoryFactors.hom.naturality_assoc (cH.hom.app X)]
  erw [reassoc_of% (square_factors F G H I e K)]
  erw [G.mapDerivedCategoryFactors.hom.naturality_assoc (cF.hom.app X)]
  congr 2
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ = DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  simp only [← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q.congr_map hc
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [R'.CommShift ℤ]
  (ρ : R ⋙ F ≅ G ⋙ R') [NatTrans.CommShift ρ.hom ℤ]
private theorem shifted_square (Y : B) (s : ℤ) :
    F.map ((R.commShiftIso s).inv.app Y) ≫ ρ.hom.app (Y⟦s⟧) ≫
      R'.map ((G.commShiftIso s).hom.app Y) ≫ (R'.commShiftIso s).hom.app (G.obj Y) =
    (F.commShiftIso s).hom.app (R.obj Y) ≫ (ρ.hom.app Y)⟦s⟧' := by
  have h := ρ.hom.shift_app_comm s Y
  simp only [Functor.commShiftIso_comp_hom_app] at h
  apply (cancel_epi (F.map ((R.commShiftIso s).hom.app Y))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Category.assoc] using h.symm
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')

private theorem shifted_single_square (Y : B) (s : ℤ) :
    F.mapDerivedCategory.map
        (((R.mapDerivedCategorySingleFunctor 0).inv.app Y)⟦s⟧' ≫
          (R.mapDerivedCategory.commShiftIso s).inv.app
            ((DerivedCategory.singleFunctor B 0).obj Y)) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor B 0).obj Y)⟦s⟧) ≫
      R'.mapDerivedCategory.map
        ((G.mapDerivedCategory.commShiftIso s).hom.app
            ((DerivedCategory.singleFunctor B 0).obj Y) ≫
          ((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦s⟧') ≫
      (R'.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor B' 0).obj (G.obj Y)) ≫
      ((R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y))⟦s⟧' =
    (F.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj (R.obj Y)) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y) ≫
        (DerivedCategory.singleFunctor A' 0).map (ρ.hom.app Y))⟦s⟧' := by
  let ρd := CategoryTheory.Functor.mapDerivedCategorySquareIso ρ
  have : NatTrans.CommShift ρd.hom ℤ := by
    dsimp only [ρd, CategoryTheory.Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have h : F.mapDerivedCategory.map ((R.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
      ρd.hom.app ((DerivedCategory.singleFunctor B 0).obj Y) ≫
      R'.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
      (R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y) ≫
        (DerivedCategory.singleFunctor A' 0).map (ρ.hom.app Y) := by
    erw [square_single R F G R' ρ Y]
    rw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
      F.mapDerivedCategory.map_id]
    erw [Category.id_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [R'.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) s]
  erw [reassoc_of% (shifted_square R.mapDerivedCategory F.mapDerivedCategory
    G.mapDerivedCategory R'.mapDerivedCategory ρd
      ((DerivedCategory.singleFunctor B 0).obj Y) s)]
  erw [F.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((R.mapDerivedCategorySingleFunctor 0).inv.app Y) s]
  simp only [← (shiftFunctor (DerivedCategory A') s).map_comp]
  rw [h]
  rfl

private theorem shifted_single_endpoints
    (Y : B) (Y' : B') {Z : A} {Z' : A'}
    (y : R.obj Y ≅ Z) (y' : R'.obj Y' ≅ Z')
    (g : G.obj Y ⟶ Y') (k : F.obj Z ⟶ Z')
    (hk : k = F.map y.inv ≫ ρ.hom.app Y ≫ R'.map g ≫ y'.hom) (s : ℤ) :
    F.mapDerivedCategory.map
        (((DerivedCategory.singleFunctor A 0).map y.inv)⟦s⟧' ≫
          ((R.mapDerivedCategorySingleFunctor 0).inv.app Y)⟦s⟧' ≫
          (R.mapDerivedCategory.commShiftIso s).inv.app
            ((DerivedCategory.singleFunctor B 0).obj Y)) ≫
      (Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor B 0).obj Y)⟦s⟧) ≫
      R'.mapDerivedCategory.map
        ((G.mapDerivedCategory.commShiftIso s).hom.app
            ((DerivedCategory.singleFunctor B 0).obj Y) ≫
          ((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦s⟧' ≫
          ((DerivedCategory.singleFunctor B' 0).map g)⟦s⟧') ≫
      (R'.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor B' 0).obj Y') ≫
      ((R'.mapDerivedCategorySingleFunctor 0).hom.app Y')⟦s⟧' ≫
      ((DerivedCategory.singleFunctor A' 0).map y'.hom)⟦s⟧' =
    (F.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj Z) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app Z)⟦s⟧' ≫
      ((DerivedCategory.singleFunctor A' 0).map k)⟦s⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  erw [R'.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((DerivedCategory.singleFunctor B' 0).map g) s]
  simp only [← (shiftFunctor (DerivedCategory A') s).map_comp_assoc]
  erw [(R'.mapDerivedCategorySingleFunctor 0).hom.naturality g]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  have hs := shifted_single_square R F G R' ρ Y s
  simp only [Functor.map_comp, Category.assoc] at hs
  erw [reassoc_of% hs]
  erw [F.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((DerivedCategory.singleFunctor A 0).map y.inv) s]
  simp only [← (shiftFunctor (DerivedCategory A') s).map_comp_assoc]
  erw [(F.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc y.inv]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  rw [hk]

end
end

private theorem shift_add_map
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (G : C ⥤ D) [G.CommShift ℤ] (Y : C) :
    G.map ((shiftFunctorAdd C (1 : ℤ) 1).inv.app Y) ≫
        (G.commShiftIso (2 : ℤ)).hom.app Y =
      (G.commShiftIso (1 : ℤ)).hom.app (Y⟦(1 : ℤ)⟧) ≫
        ((G.commShiftIso (1 : ℤ)).hom.app Y)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd D (1 : ℤ) 1).inv.app (G.obj Y) := by
  change G.map ((shiftFunctorAdd C (1 : ℤ) 1).inv.app Y) ≫
    (G.commShiftIso ((1 : ℤ) + 1)).hom.app Y = _
  rw [G.commShiftIso_add]
  simp only [Functor.CommShift.isoAdd_hom_app, ← G.map_comp_assoc,
    Iso.inv_hom_id_app]
  rw [G.map_id, Category.id_comp]

private theorem shifted_arrow_square
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ]
    {A B : C} {A' B' : D} (w : A ⟶ B⟦(1 : ℤ)⟧) (w' : A' ⟶ B'⟦(1 : ℤ)⟧)
    (a : F.obj A ⟶ A') (b : F.obj B ⟶ B')
    (h : F.map w ≫ (F.commShiftIso (1 : ℤ)).hom.app B ≫ b⟦(1 : ℤ)⟧' = a ≫ w') :
    F.map (w⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd C (1 : ℤ) 1).inv.app B) ≫
        (F.commShiftIso (2 : ℤ)).hom.app B ≫ b⟦(2 : ℤ)⟧' =
      (F.commShiftIso (1 : ℤ)).hom.app A ≫ a⟦(1 : ℤ)⟧' ≫ w'⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd D (1 : ℤ) 1).inv.app B' := by
  rw [F.map_comp, Category.assoc, reassoc_of% (shift_add_map F B)]
  simp only [← Category.assoc]
  rw [F.commShiftIso_hom_naturality w (1 : ℤ)]
  simp only [Category.assoc]
  have hb := (shiftFunctorAdd D (1 : ℤ) 1).inv.naturality b
  change b⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd D (1 : ℤ) 1).inv.app B' =
    (shiftFunctorAdd D (1 : ℤ) 1).inv.app (F.obj B) ≫ b⟦(2 : ℤ)⟧' at hb
  rw [← hb]
  simp only [← (shiftFunctor D (1 : ℤ)).map_comp_assoc]
  rw [h]

private theorem ses_boundary_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex C} {S' : ShortComplex D}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (k : F.mapShortComplex.obj S ⟶ S') :
    F.mapDerivedCategory.map hS.singleδ ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj S.X₁) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁ ≫
          (DerivedCategory.singleFunctor D 0).map k.τ₁)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫
        (DerivedCategory.singleFunctor D 0).map k.τ₃ ≫ hS'.singleδ := by
  have hδ :
      F.mapDerivedCategory.map hS.singleδ ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj S.X₁) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫
        (hS.map_of_exact F).singleδ := by
    have hh := hS.mapShiftedHom_singleδ' F
    apply (cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃)).1
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, ShiftedHom.map] using hh
  simp only [Functor.map_comp]
  erw [reassoc_of% hδ]
  have hk := (ShortComplex.ShortExact.singleTriangle.map (hS.map_of_exact F) hS' k).comm₃
  change (hS.map_of_exact F).singleδ ≫
      ((DerivedCategory.singleFunctor D 0).map k.τ₁)⟦(1 : ℤ)⟧' =
    (DerivedCategory.singleFunctor D 0).map k.τ₃ ≫ hS'.singleδ at hk
  simpa only [Category.assoc] using
    congrArg ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫ ·) hk

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
private theorem arrow_normalized_square
    (U V : A) (U' V' : A')
    (w : (DerivedCategory.singleFunctor A 0).obj U ⟶
      ((DerivedCategory.singleFunctor A 0).obj V)⟦(1 : ℤ)⟧)
    (w' : (DerivedCategory.singleFunctor A' 0).obj U' ⟶
      ((DerivedCategory.singleFunctor A' 0).obj V')⟦(1 : ℤ)⟧)
    (T : B) (T' : B') (y : R.obj T ≅ V) (y' : R'.obj T' ≅ V')
    (g : G.obj T ⟶ T') (b : F.obj V ⟶ V')
    (hk : b = F.map y.inv ≫ ρ.hom.app T ≫ R'.map g ≫ y'.hom)
    (a : F.obj U ⟶ U')
    (hδ : F.mapDerivedCategory.map w ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor A 0).obj V) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app V ≫
          (DerivedCategory.singleFunctor A' 0).map b)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app U ≫
        (DerivedCategory.singleFunctor A' 0).map a ≫ w')
    (t : ((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧ ⟶
      R.mapDerivedCategory.obj (((DerivedCategory.singleFunctor B 0).obj T)⟦(2 : ℤ)⟧))
    (t' : ((DerivedCategory.singleFunctor A' 0).obj U')⟦(1 : ℤ)⟧ ⟶
      R'.mapDerivedCategory.obj (((DerivedCategory.singleFunctor B' 0).obj T')⟦(2 : ℤ)⟧))
    (ht : t ≫ (R.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor B 0).obj T) ≫
        ((R.mapDerivedCategorySingleFunctor 0).hom.app T)⟦(2 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A 0).map y.hom)⟦(2 : ℤ)⟧' =
      w⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor A 0).obj V))
    (ht' : t' ≫ (R'.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor B' 0).obj T') ≫
        ((R'.mapDerivedCategorySingleFunctor 0).hom.app T')⟦(2 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A' 0).map y'.hom)⟦(2 : ℤ)⟧' =
      w'⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd (DerivedCategory A') (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor A' 0).obj V'))
    (aD : F.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor A' 0).obj U')⟦(1 : ℤ)⟧)
    (gD : G.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor B 0).obj T)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor B' 0).obj T')⟦(2 : ℤ)⟧)
    (haD : aD = (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor A 0).obj U) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app U)⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor A' 0).map a)⟦(1 : ℤ)⟧')
    (hgD : gD = (G.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor B 0).obj T) ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app T ≫
        (DerivedCategory.singleFunctor B' 0).map g)⟦(2 : ℤ)⟧') :
    F.mapDerivedCategory.map t ≫ (Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor B 0).obj T)⟦(2 : ℤ)⟧) ≫
        R'.mapDerivedCategory.map gD = aD ≫ t' := by
  rw [haD, hgD]
  let e := (R.mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor B 0).obj T) ≪≫
    (shiftFunctor (DerivedCategory A) (2 : ℤ)).mapIso
      ((R.mapDerivedCategorySingleFunctor 0).app T ≪≫
        (DerivedCategory.singleFunctor A 0).mapIso y)
  let e' := (R'.mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor B' 0).obj T') ≪≫
    (shiftFunctor (DerivedCategory A') (2 : ℤ)).mapIso
      ((R'.mapDerivedCategorySingleFunctor 0).app T' ≪≫
        (DerivedCategory.singleFunctor A' 0).mapIso y')
  have ht0 : t ≫ e.hom = w⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor A 0).obj V) := by
    simpa only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using ht
  have ht0' : t' ≫ e'.hom = w'⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory A') (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor A' 0).obj V') := by
    simpa only [e', Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using ht'
  have ht1 : t = (w⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor A 0).obj V)) ≫ e.inv := by
    rw [← ht0, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he := shifted_single_endpoints R F G R' ρ T T' y y' g b hk (2 : ℤ)
  have he' : F.mapDerivedCategory.map e.inv ≫
      (Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor B 0).obj T)⟦(2 : ℤ)⟧) ≫
      R'.mapDerivedCategory.map
        ((G.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor B 0).obj T) ≫
          ((G.mapDerivedCategorySingleFunctor 0).hom.app T ≫
            (DerivedCategory.singleFunctor B' 0).map g)⟦(2 : ℤ)⟧') ≫ e'.hom =
    (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor A 0).obj V) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app V)⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor A' 0).map b)⟦(2 : ℤ)⟧' := by
    simpa only [e, e', Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc] using he
  apply (cancel_mono e'.hom).1
  rw [ht1, Functor.map_comp]
  simp only [Category.assoc]
  rw [he', ht0']
  have hδ' := shifted_arrow_square F.mapDerivedCategory w w'
    ((F.mapDerivedCategorySingleFunctor 0).hom.app U ≫
      (DerivedCategory.singleFunctor A' 0).map a)
    ((F.mapDerivedCategorySingleFunctor 0).hom.app V ≫
      (DerivedCategory.singleFunctor A' 0).map b)
      (by simpa only [Category.assoc] using hδ)
  simpa only [Functor.map_comp, Category.assoc] using hδ'

end

private def mkBoundary
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {U P V : C} (i : V ⟶ P) (p : P ⟶ U) (z : i ≫ p = 0)
    (hs : (ShortComplex.mk i p z).ShortExact) :
    (DerivedCategory.singleFunctor C 0).obj U ⟶
      ((DerivedCategory.singleFunctor C 0).obj V)⟦(1 : ℤ)⟧ := hs.singleδ

private theorem mk_boundary_square
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {U P V : C} (i : V ⟶ P) (p : P ⟶ U) (z : i ≫ p = 0)
    (hs : (ShortComplex.mk i p z).ShortExact)
    {U' P' V' : D} (i' : V' ⟶ P') (p' : P' ⟶ U') (z' : i' ≫ p' = 0)
    (hs' : (ShortComplex.mk i' p' z').ShortExact)
    (k : F.mapShortComplex.obj (ShortComplex.mk i p z) ⟶ ShortComplex.mk i' p' z') :
    F.mapDerivedCategory.map (mkBoundary i p z hs) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj V) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app V ≫
          (DerivedCategory.singleFunctor D 0).map
            (X := F.obj V) (Y := V') k.τ₁)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app U ≫
        (DerivedCategory.singleFunctor D 0).map
          (X := F.obj U) (Y := U') k.τ₃ ≫ mkBoundary i' p' z' hs' := by
  exact ses_boundary_square F hs hs' k

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapHomologicalComplex HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory

-- Match the localization instances used by ChernData.rootIso and Reduction.model.
attribute [local instance 100000] AlgebraicGeometry.ProEtale.SpTowerClasses.abDerived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
attribute [local irreducible] AlgebraicGeometry.ProEtale.SpTowerClasses.abDerived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

open Opposite WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def kummerBoundary {T : Scheme.{u}} (q : Kummer l T) :
    (DerivedCategory.singleFunctor (Ab T) 0).obj (units T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (roots l T))⟦(1 : ℤ)⟧ :=
  q.boundary

private theorem kummerBoundarySquare {X Y : Scheme.{u}}
    (F : Ab Y ⥤ Ab X) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (qY : Kummer l Y) (qX : Kummer l X)
    (k : F.mapShortComplex.obj
        qY.shortComplex ⟶
      qX.shortComplex) :
    F.mapDerivedCategory.map (kummerBoundary l qY) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Ab Y) 0).obj (roots l Y)) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app (roots l Y) ≫
          (DerivedCategory.singleFunctor (Ab X) 0).map
            (X := F.obj (roots l Y)) (Y := roots l X) k.τ₁)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (units Y) ≫
        (DerivedCategory.singleFunctor (Ab X) 0).map
          (X := F.obj (units Y)) (Y := units X) k.τ₃ ≫ kummerBoundary l qX := by
  exact mk_boundary_square F qY.inclusion qY.power qY.zero qY.exact
    qX.inclusion qX.power qX.zero qX.exact k

private theorem units_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    unitsDerivedPull f =
      ((abPull f).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y)) ≫
        (((abPull f).mapDerivedCategorySingleFunctor 0).hom.app (units Y))⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor (Ab X) 0).map (unitsPull f))⟦(1 : ℤ)⟧' := by rfl

private theorem root_comparison
    {X Y : Scheme.{u}} {f : X ⟶ Y} {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    (d.derivedRoot 2).hom =
      (d.pull.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Systems Y (Rrings l Y)) 0).obj cY.rootModule) ≫
        ((d.pull.mapDerivedCategorySingleFunctor 0).hom.app cY.rootModule ≫
          (DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).map
            d.rootIso.hom)⟦(2 : ℤ)⟧' := by
  rfl

private def chernRootTranspose
    (T : Scheme.{u})
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (c : ChernData l T R A φ)
    : ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧ ⟶
      c.reduction.forget.F.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (Systems T R) 0).obj c.rootModule)⟦(2 : ℤ)⟧) :=
  (c.reduction.derivedAdjunction.homEquiv _ _) c.rootIso.hom

-- Keep the coefficient diagrams abstract while matching the Chern record fields.
private theorem chern_boundary_models
    {X Y : Scheme.{u}}
    (RY AY : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (φY : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
        (fun n ↦ RY.obj (op n)) (fun n ↦ RY.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
        (fun n ↦ AY.obj (op n)) (fun n ↦ AY.map (homOfLE (Nat.le_succ n)).op))
    (RX AX : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (φX : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (fun n ↦ RX.obj (op n)) (fun n ↦ RX.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (fun n ↦ AX.obj (op n)) (fun n ↦ AX.map (homOfLE (Nat.le_succ n)).op))
    (cY : ChernData l Y RY AY φY) (cX : ChernData l X RX AX φX)
    (F : Ab Y ⥤ Ab X) (G : Systems Y RY ⥤ Systems X RX)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (ρ : cY.reduction.forget.F ⋙ F ≅ G ⋙ cX.reduction.forget.F)
    (g : G.obj cY.rootModule ⟶ cX.rootModule)
    (b : F.obj (roots l Y) ⟶ roots l X)
    (hk : b = F.map cY.rootForget.inv ≫ ρ.hom.app cY.rootModule ≫
      cX.reduction.forget.F.map g ≫ cX.rootForget.hom)
    (a : F.obj (units Y) ⟶ units X)
    (hδ : F.mapDerivedCategory.map (kummerBoundary l cY.kummer) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (Ab Y) 0).obj (roots l Y)) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app (roots l Y) ≫
          (DerivedCategory.singleFunctor (Ab X) 0).map b)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (units Y) ≫
        (DerivedCategory.singleFunctor (Ab X) 0).map a ≫ kummerBoundary l cX.kummer)
    (hY : cY.rootNormalized l Y RY AY φY)
    (hX : cX.rootNormalized l X RX AX φX)
    (aD : F.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Ab X) 0).obj (units X))⟦(1 : ℤ)⟧)
    (gD : G.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (Systems Y RY) 0).obj cY.rootModule)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Systems X RX) 0).obj cX.rootModule)⟦(2 : ℤ)⟧)
    (haD : aD = (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y)) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app (units Y))⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor (Ab X) 0).map a)⟦(1 : ℤ)⟧')
    (hgD : gD = (G.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Systems Y RY) 0).obj cY.rootModule) ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app cY.rootModule ≫
        (DerivedCategory.singleFunctor (Systems X RX) 0).map g)⟦(2 : ℤ)⟧') :
    F.mapDerivedCategory.map
        ((cY.reduction.derivedAdjunction.homEquiv _ _) cY.rootIso.hom) ≫
      (Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor (Systems Y RY) 0).obj
          cY.rootModule)⟦(2 : ℤ)⟧) ≫
      cX.reduction.forget.F.mapDerivedCategory.map gD =
    aD ≫ (cX.reduction.derivedAdjunction.homEquiv _ _) cX.rootIso.hom := by
  exact arrow_normalized_square cY.reduction.forget.F F G cX.reduction.forget.F ρ
    (units Y) (roots l Y) (units X) (roots l X)
    (kummerBoundary l cY.kummer) (kummerBoundary l cX.kummer)
    cY.rootModule cX.rootModule cY.rootForget cX.rootForget g b hk a hδ
    (chernRootTranspose l Y RY AY φY cY) (chernRootTranspose l X RX AX φX cX)
    (chern_root_normalization_equation l Y RY AY φY cY hY)
    (chern_root_normalization_equation l X RX AX φX cX hX) aD gD haD hgD

/-- The normalized positive Kummer-boundary transpose square commutes under inverse image.

Source: classes (2), naturality of the positive Kummer boundary
(blueprint: lem-sp-tower-kummer-pullback-transpose).

Proof: transport the short-exact-sequence boundary through the exact inverse
image using its canonical single and shift comparisons. Naturality of the
triangle under d.kummer identifies its first and last components with the
recorded root and units pullback maps. Shift once more using commShiftIso_add.
The two target normalizations identify these signed shifted boundaries with
the adjunction transposes of the recorded root isomorphisms. Cancel the
invertible single and shift comparisons to obtain the stated square. -/
theorem kummer_pullback_transpose
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (nY : cY.Normalized l E) (nX : cX.Normalized l E)
    (d : IntegralCoefficientPullback l E f cY cX) :
    (abPull f).mapDerivedCategory.map
        ((cY.reduction.derivedAdjunction.homEquiv _ _) cY.rootIso.hom) ≫
      (Functor.mapDerivedCategorySquareIso d.forgetIso).hom.app
        (((DerivedCategory.singleFunctor (Systems Y (Rrings l Y)) 0).obj
          cY.rootModule)⟦(2 : ℤ)⟧) ≫
      cX.reduction.forget.F.mapDerivedCategory.map (d.derivedRoot 2).hom =
    unitsDerivedPull f ≫
      (cX.reduction.derivedAdjunction.homEquiv _ _) cX.rootIso.hom := by
  exact chern_boundary_models l
    (Rrings l Y) (Arings l E Y) (coefficientSystemMap l E Y)
    (Rrings l X) (Arings l E X) (coefficientSystemMap l E X) cY cX
    (abPull f) d.pull d.forgetIso d.rootIso.hom d.kummer.τ₁ d.kummer_roots
    (unitsPull f)
    (by simpa only [d.kummer_units] using
      kummerBoundarySquare l (abPull f) cY.kummer cX.kummer d.kummer)
    (chern_target_normalization l E cY nY) (chern_target_normalization l E cX nX)
    (unitsDerivedPull f) (d.derivedRoot 2).hom
    (units_comparison f) (root_comparison l E d)

end AlgebraicGeometry.ProEtale.SpTowerClasses
