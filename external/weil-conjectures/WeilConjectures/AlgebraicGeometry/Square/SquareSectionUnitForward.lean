/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageSectionUnit
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareUnitMap
public import WeilConjectures.AlgebraicGeometry.Square.SquareResolutionRoofModels
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.NormalizedDirectImageSquareUnit
import WeilConjectures.AlgebraicGeometry.Injective.InjectiveSectionUnitComparison
import all WeilConjectures.AlgebraicGeometry.Local.LocalHypercohomologyClassUnit
import all WeilConjectures.AlgebraicGeometry.Direct.DirectImageComplexUnit
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-! # Forward normalized square comparison before endpoint cancellation

Source: Stacks Project, Cohomology, Tags 0D5T and 0D5X.
(blueprint: lem-weil-pbc-square-section-unit-forward).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

section Helpers

local instance squareSectionUnitForwardCategory (Y : Scheme.{u}) : Category Y.Modules :=
  inferInstanceAs (Category (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
local instance squareSectionUnitForwardAbelian (Y : Scheme.{u}) : Abelian Y.Modules :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
local instance squareSectionUnitForwardHasDerivedCategory (Y : Scheme.{u}) :
    HasDerivedCategory.{w} Y.Modules :=
  inferInstanceAs (HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory Scheme.Modules.instAbelian TopCat.Sheaf
  Scheme.Modules.pushforward RingedSpace.moduleDirectImage
  HomologicalComplex.homologyFunctor
  RingedSpace.openModuleSections HomologicalComplex.homologyMap
  Scheme.Hom.toRingCatSheafHom SheafOfModules.pushforward SheafOfModules.forget
  SheafOfModules.toSheaf PresheafOfModules.toPresheaf HomologicalComplex.homology
  HomologicalComplex.shortComplexFunctor
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  RingedSpace.topEdgeLocalModel RingedSpace.topEdgeInverseModel

private theorem square_mate_eq {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g) :
    (derivedSquareRightComparison f k g v h).hom =
      (schemeNormalizedDirectImageCompIso v f).hom ≫
        eqToHom (congrArg (fun a ↦ schemeDerivedDirectImage a) h) ≫
          (schemeNormalizedDirectImageCompIso k g).inv := by
  exact derivedDirectImage_square_mate f k g v h

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem quotient_hom
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := by rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem quotient_inv
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).inv.app K = 𝟙 _ := by rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem unitQ_eq {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ I =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I) := by
  unfold Functor.rightDerivedFunctorUnitQ
  erw [quotient_inv, Category.id_comp, quotient_hom,
    F.rightDerivedFunctor.map_id, Category.comp_id]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
-- Normalize the composite unit before specializing its categories to scheme modules.
private theorem squareForward_compUnitQ_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] (I : CochainComplex C ℤ) :
    (Functor.rightDerivedFunctorCompUnit F G).app
        ((HomotopyCategory.quotient C (.up ℤ)).obj I) =
      G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnitQ I) := by
  rw [unitQ_eq, unitQ_eq]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, DerivedCategory.Qh.map_id]
  erw [Category.id_comp]
  rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem squareForward_compUnit_square
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    [Abelian C] [Abelian D] [Abelian E] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions E]
    (F : C ⥤ D) (G : D ⥤ A) (F' : C ⥤ E) (G' : E ⥤ A)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    (α : F ⋙ G ⟶ F' ⋙ G')
    (β : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ⟶
      F'.rightDerivedFunctor ⋙ G'.rightDerivedFunctor)
    (h : Functor.rightDerivedFunctorCompUnit F G ≫ Functor.whiskerLeft DerivedCategory.Qh β =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory α (.up ℤ)) DerivedCategory.Qh ≫
        Functor.rightDerivedFunctorCompUnit F' G') (I : CochainComplex C ℤ) :
    G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnitQ I) ≫
      β.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I) ≫
      G'.rightDerivedFunctorUnitQ ((F'.mapHomologicalComplex (.up ℤ)).obj I) ≫
      G'.rightDerivedFunctor.map (F'.rightDerivedFunctorUnitQ I) := by
  have hh := congr_app h ((HomotopyCategory.quotient C (.up ℤ)).obj I)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    squareForward_compUnitQ_app, NatTrans.mapHomotopyCategory_app, Category.assoc] at hh
  exact hh

private theorem square_unitQ {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (I : CochainComplex Z.Modules ℤ) :
    (pushforward f).rightDerivedFunctorUnitQ
        (((pushforward v).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (schemeDerivedDirectImage f).map ((pushforward v).rightDerivedFunctorUnitQ I) ≫
      (derivedSquareRightComparison f k g v h).hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
        (.up ℤ)).app I) ≫
      (pushforward g).rightDerivedFunctorUnitQ
        (((pushforward k).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (schemeDerivedDirectImage g).map ((pushforward k).rightDerivedFunctorUnitQ I) := by
  have hh := squareForward_compUnit_square (pushforward v) (pushforward f)
    (pushforward k) (pushforward g)
    (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
    (schemeNormalizedDirectImageCompIso v f ≪≫
      eqToIso (congrArg (fun a ↦ schemeDerivedDirectImage a) h) ≪≫
      (schemeNormalizedDirectImageCompIso k g).symm).hom
    (normalizedDirectImageSquare_unit f k g v h) I
  rw [square_mate_eq]
  exact hh

private theorem squareForward_inverseOpenUnitQ_eq {X S : Scheme.{u}} (f : X ⟶ S) :
    RingedSpace.inverseOpenUnitQ f.toLRSHom.toShHom =
      localComplexUnit (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.localAbelianSections S.toRingedSpace)
        (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace) := by
  unfold RingedSpace.inverseOpenUnitQ localComplexUnit
  rfl

private theorem sections_unit {X S : Scheme.{u}} (f : X ⟶ S)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (RingedSpace.inverseOpenUnitQ f.toLRSHom.toShHom).app K ≫
      (RingedSpace.localLerayComparison f.toLRSHom.toShHom).app (DerivedCategory.Q.obj K) ≫
      (RingedSpace.derivedLocalAbelianSections S.toRingedSpace).map
        ((RingedSpace.sectionStandardDirectImageIso f.toLRSHom.toShHom).hom.app
          (DerivedCategory.Q.obj K)) =
    ((RingedSpace.localAbelianSections S.toRingedSpace).rightDerivedFunctorOfQuasiIsoResolutionsUnit
      (RingedSpace.localSectionsEnoughKInjectives S.toRingedSpace)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).obj K)) ≫
      (RingedSpace.derivedLocalAbelianSections S.toRingedSpace).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnitQ K) := by
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let F := RingedSpace.localAbelianSections S.toRingedSpace
  let RF := RingedSpace.derivedLocalAbelianSections S.toRingedSpace
  have hfac := NatTrans.congr_app (Classical.choose_spec
    ((Functor.rightDerivedFunctorOfQuasiIsoResolutions_universal (D ⋙ F)
      (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace)
      (RingedSpace.sectionDerivedDirectImage f.toLRSHom.toShHom ⋙ RF)).surjective
        (RingedSpace.localLerayCompositeUnit f.toLRSHom.toShHom)))
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  have hstd := NatTrans.congr_app
    (RingedSpace.sectionStandardDirectImageIso_fac f.toLRSHom.toShHom)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  rw [squareForward_inverseOpenUnitQ_eq, localComplexUnit_app_eq, unitQ_eq]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hfac hstd
  erw [reassoc_of% hfac]
  simp only [RingedSpace.localLerayCompositeUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, CategoryTheory.Functor.map_id,
    Category.assoc]
  erw [← RF.map_comp, hstd, Category.id_comp]
  rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private def cochainSectionUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) (q : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h ⋙
        DerivedCategory.homologyFunctor D q :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.homologyFunctorFactors D q).inv ≫
    Functor.whiskerRight (localComplexUnit F h) (DerivedCategory.homologyFunctor D q)

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem cochainSectionUnit_model
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) (q : ℤ)
    (B I : CochainComplex C ℤ) [I.IsKInjective] (b : B ⟶ I) :
    (cochainSectionUnit F h q).app B ≫
      (DerivedCategory.homologyFunctor D q).map
        ((F.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map b)) ≫
      (DerivedCategory.homologyFunctor D q).map
        (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)).hom ≫
      (DerivedCategory.homologyFunctorFactors D q).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I) =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map b) q := by
  let H := DerivedCategory.homologyFunctor D q
  have hn := (cochainSectionUnit F h q).naturality b
  have hu := localComplexUnit_resolution F h (𝟙 I)
  have hi : (cochainSectionUnit F h q).app I ≫
      H.map (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)).hom ≫
      (DerivedCategory.homologyFunctorFactors D q).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I) = 𝟙 _ := by
    dsimp only [cochainSectionUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    rw [Category.assoc, ← H.map_comp_assoc, hu]
    erw [(F.mapHomologicalComplex (.up ℤ)).map_id, DerivedCategory.Q.map_id, H.map_id,
      Category.id_comp]
    exact (DerivedCategory.homologyFunctorFactors D q).inv_hom_id_app
      ((F.mapHomologicalComplex (.up ℤ)).obj I)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hi]
  exact Category.comp_id _

private def cochainLocalSectionUnit (S : Scheme.{u}) (q : ℤ) :
    (RingedSpace.localAbelianSections S.toRingedSpace).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℤ) q ⟶
      DerivedCategory.Q ⋙ RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q :=
  Functor.whiskerLeft
      ((RingedSpace.localAbelianSections S.toRingedSpace).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.homologyFunctorFactors _ q).inv ≫
    Functor.whiskerRight (localComplexUnit
      (RingedSpace.localAbelianSections S.toRingedSpace)
      (RingedSpace.localSectionsEnoughKInjectives S.toRingedSpace))
      (DerivedCategory.homologyFunctor _ q)

private def cochainLocalSectionUnitAt (S : Scheme.{u}) (q : ℤ) (V : S.Opens)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
      (.up ℤ)).obj K).homology q ⟶
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).obj
        (DerivedCategory.Q.obj K)).obj (op V) :=
  let F := RingedSpace.localAbelianSections S.toRingedSpace
  let E := (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  ((((F.mapHomologicalComplex (.up ℤ)).obj K).sc q).mapHomologyIso E).hom ≫
    ((cochainLocalSectionUnit S q).app K).app (op V)

private theorem sections_unitAt {X S : Scheme.{u}} (f : X ⟶ S) (q : ℤ)
    (V : S.Opens)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    directImageSectionUnitAt f q V K =
      cochainLocalSectionUnitAt S q V
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj K) ≫
        ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
          ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnitQ K)).app
            (op V) := by
  let H := DerivedCategory.homologyFunctor (S.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) q
  have hu := congrArg (fun z ↦ (H.map z).app (op V)) (sections_unit f K)
  unfold directImageSectionUnitAt directImageSectionUnit cochainLocalSectionUnitAt
    cochainLocalSectionUnit RingedSpace.directImageSectionComparison
    RingedSpace.localHypercohomologyComparison
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    H, Functor.map_comp, Category.assoc, localComplexUnit_app_eq] at hu ⊢
  exact congrArg (fun z ↦
    (((((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
      RingedSpace.localAbelianSections S.toRingedSpace).mapHomologicalComplex (.up ℤ)).obj
        K).sc q).mapHomologyIso
          ((CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom ≫
      ((DerivedCategory.homologyFunctorFactors (S.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) q).inv.app
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          RingedSpace.localAbelianSections S.toRingedSpace).mapHomologicalComplex
            (.up ℤ)).obj K)).app (op V) ≫ z) hu

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem squareForward_map_pasting {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {B I K : C} {PB PI PK : D}
    (u : PB ⟶ PK) (v : B ⟶ K) (e : PK ≅ PI) (r : K ≅ I)
    (c : PB ⟶ F.obj B) (d : PI ⟶ F.obj I) (p : PB ⟶ PI) (q : B ⟶ I)
    (hp : u ≫ e.hom = p) (hq : v ≫ r.hom = q)
    (hn : p ≫ d = c ≫ F.map q) :
    u ≫ (e.hom ≫ d ≫ F.map r.inv) = c ≫ F.map v := by
  rw [← Category.assoc u e.hom, hp, ← Category.assoc, hn, Category.assoc,
    ← F.map_comp, ← hq, Category.assoc, r.hom_inv_id, Category.comp_id]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
-- Compare the units on an arbitrary K-injective representative. This keeps the
-- functorial resolution construction out of the naturality and cancellation proofs.
private theorem squareForward_cochain_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (P : C ⥤ E) (W : D ⥤ E) [F.Additive] [P.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) (q : ℤ)
    (c : P.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor E (.up ℤ) q ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) q ⋙ W)
    (B I : CochainComplex C ℤ) [I.IsKInjective] (K : DerivedCategory C)
    (r : DerivedCategory.Q.obj I ≅ K) (a : DerivedCategory.Q.obj B ⟶ K) :
    let HD := DerivedCategory.homologyFunctor D q
    let HE := DerivedCategory.homologyFunctor E q
    let RF := F.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ HD
    let RP := P.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ HE
    let e := RP.mapIso r.symm ≪≫
      HE.mapIso (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)) ≪≫
      (DerivedCategory.homologyFunctorFactors E q).app
        ((P.mapHomologicalComplex (.up ℤ)).obj I)
    let t := RF.mapIso r.symm ≪≫
      HD.mapIso (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)) ≪≫
      (DerivedCategory.homologyFunctorFactors D q).app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)
    (cochainSectionUnit P h q).app B ≫ RP.map a ≫ e.hom ≫ c.app I ≫ W.map t.inv =
      c.app B ≫ W.map ((cochainSectionUnit F h q).app B ≫ RF.map a) := by
  dsimp only
  obtain ⟨b, hb⟩ := RingedSpace.exists_complex_map_into_kInjective B I (a ≫ r.inv)
  have hp := cochainSectionUnit_model P h q B I b
  have hf := cochainSectionUnit_model F h q B I b
  let e := (P.rightDerivedFunctorOfQuasiIsoResolutions h ⋙
      DerivedCategory.homologyFunctor E q).mapIso r.symm ≪≫
    (DerivedCategory.homologyFunctor E q).mapIso
      (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)) ≪≫
    (DerivedCategory.homologyFunctorFactors E q).app
      ((P.mapHomologicalComplex (.up ℤ)).obj I)
  let t := (F.rightDerivedFunctorOfQuasiIsoResolutions h ⋙
      DerivedCategory.homologyFunctor D q).mapIso r.symm ≪≫
    (DerivedCategory.homologyFunctor D q).mapIso
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)) ≪≫
    (DerivedCategory.homologyFunctorFactors D q).app
      ((F.mapHomologicalComplex (.up ℤ)).obj I)
  have hp' : (cochainSectionUnit P h q).app B ≫
      (P.rightDerivedFunctorOfQuasiIsoResolutions h ⋙
        DerivedCategory.homologyFunctor E q).map a ≫ e.hom =
      HomologicalComplex.homologyMap ((P.mapHomologicalComplex (.up ℤ)).map b) q := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
    rw [← Functor.map_comp_assoc, ← hb]
    exact hp
  have hf' : (cochainSectionUnit F h q).app B ≫
      (F.rightDerivedFunctorOfQuasiIsoResolutions h ⋙
        DerivedCategory.homologyFunctor D q).map a ≫ t.hom =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map b) q := by
    dsimp only [t, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
    rw [← Functor.map_comp_assoc, ← hb]
    exact hf
  rw [← Category.assoc]
  exact squareForward_map_pasting W _ _ e t (c.app B) (c.app I) _ _
    ((Category.assoc _ _ _).trans hp') ((Category.assoc _ _ _).trans hf') (c.naturality b)

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
-- Explicit components identify the two cochain carriers one complex at a time.
private def squareForward_cochainComparison {X S : Scheme.{u}} (f : X ⟶ S) (q : ℤ) :
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
      RingedSpace.localAbelianSections S.toRingedSpace).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (S.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℤ) q ⟶
      (RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℤ) q ⋙
        (Functor.whiskeringLeft S.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
          (TopologicalSpace.Opens.map f.base).op := by
  let F := RingedSpace.localAbelianSections X.toRingedSpace
  let W := (Functor.whiskeringLeft S.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (TopologicalSpace.Opens.map f.base).op
  refine
    { app := fun B ↦ (W.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj B)
      naturality := ?_ }
  intro B I b
  convert (W.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map b) using 1 <;> rfl

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem inverseOpen_unit {X S : Scheme.{u}} (f : X ⟶ S) (q : ℤ)
    (B : CochainComplex X.Modules ℤ) (K : schemeDerivedCategory X)
    (a : DerivedCategory.Q.obj B ⟶ K) :
    let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
      RingedSpace.localAbelianSections S.toRingedSpace
    let W := (Functor.whiskeringLeft S.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op
    (cochainSectionUnit P (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace) q).app B ≫
      (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom q).map a ≫
      (squareInverseOpenComparison f q K).hom =
    (W.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app
        (((RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex
          (.up ℤ)).obj B) ≫
      W.map ((cochainLocalSectionUnit X q).app B ≫
        (RingedSpace.localHypercohomologyPresheaf X.toRingedSpace q).map a) := by
  dsimp only
  let F := RingedSpace.localAbelianSections X.toRingedSpace
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections S.toRingedSpace
  let W := (Functor.whiskeringLeft S.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (TopologicalSpace.Opens.map f.base).op
  let I := RingedSpace.topEdgeResolution X.toRingedSpace K
  have : I.IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (DerivedCategory.Q.objPreimage K)
  unfold squareInverseOpenComparison RingedSpace.topEdgeInverseModel RingedSpace.topEdgeLocalModel
  exact squareForward_cochain_comparison F P W
    (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace) q
    (squareForward_cochainComparison f q) B I K
    (RingedSpace.topEdgeResolutionIso X.toRingedSpace K) a

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem sections_to_inverse {X S : Scheme.{u}} (f : X ⟶ S) (q : ℤ)
    (B : CochainComplex X.Modules ℤ) (K : schemeDerivedCategory X)
    (a : DerivedCategory.Q.obj B ⟶ K) :
    let W := (Functor.whiskeringLeft S.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map f.base).op
    (directImageSectionUnit f q).app B ≫
      (RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
        ((schemeDerivedDirectImage f).map a) ≫
      (RingedSpace.topEdgeLocalLeray f.toLRSHom.toShHom q K).hom ≫
      (squareInverseOpenComparison f q K).hom =
    (W.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app
        (((RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex
          (.up ℤ)).obj B) ≫
      W.map ((cochainLocalSectionUnit X q).app B ≫
        (RingedSpace.localHypercohomologyPresheaf X.toRingedSpace q).map a) := by
  dsimp only
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections S.toRingedSpace
  have hn := (RingedSpace.directImageSectionComparison f.toLRSHom.toShHom q).naturality a
  change (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom q).map a ≫
      (RingedSpace.directImageSectionComparison f.toLRSHom.toShHom q).app K =
    (RingedSpace.directImageSectionComparison f.toLRSHom.toShHom q).app
        (DerivedCategory.Q.obj B) ≫
      (RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
        ((schemeDerivedDirectImage f).map a) at hn
  rw [show (directImageSectionUnit f q).app B =
      (cochainSectionUnit P (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace) q).app
          B ≫
        (RingedSpace.directImageSectionComparison f.toLRSHom.toShHom q).app
          (DerivedCategory.Q.obj B) by
    dsimp only [directImageSectionUnit, cochainSectionUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [squareForward_inverseOpenUnitQ_eq, Category.assoc]]
  with_unfolding_all
    erw [Category.assoc, ← reassoc_of% hn,
      RingedSpace.directImageSectionComparison_eq]
  simp only [Iso.inv_hom_id_assoc]
  exact inverseOpen_unit f q B K a

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem sections_to_inverseAt {X S : Scheme.{u}} (f : X ⟶ S) (q : ℤ)
    (V : S.Opens) (B : CochainComplex X.Modules ℤ) (K : schemeDerivedCategory X)
    (a : DerivedCategory.Q.obj B ⟶ K) :
    directImageSectionUnitAt f q V B ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
        ((schemeDerivedDirectImage f).map a)).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray f.toLRSHom.toShHom q K).hom.app (op V) ≫
      (squareInverseOpenComparison f q K).hom.app (op V) =
    cochainLocalSectionUnitAt X q (f ⁻¹ᵁ V) B ≫
      ((RingedSpace.localHypercohomologyPresheaf X.toRingedSpace q).map a).app
        (op (f ⁻¹ᵁ V)) := by
  let F := RingedSpace.localAbelianSections X.toRingedSpace
  let W := (Functor.whiskeringLeft S.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    (TopologicalSpace.Opens.map f.base).op
  let E := (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have he := (((F.mapHomologicalComplex (.up ℤ)).obj B).sc q).mapHomologyIso_comp_hom W E
  unfold directImageSectionUnitAt cochainLocalSectionUnitAt
  simp only [Category.assoc]
  erw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.comp_app]
  erw [sections_to_inverse f q B K a]
  dsimp [Functor.mapHomologicalComplexHomologyIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso,
    ShortComplex.homologyFunctorIso, HomologicalComplex.homologyFunctorIso]
  simp only [ShortComplex.homologyMap_id, NatTrans.id_app, Category.id_comp,
    Category.assoc]
  try erw [Category.id_comp]
  try erw [Category.id_comp]
  with_unfolding_all erw [← reassoc_of% he]
  rfl

private theorem cochainLocalSectionUnitAt_naturality (S : Scheme.{u}) (q : ℤ)
    (V : S.Opens) {K L : CochainComplex S.Modules ℤ} (a : K ⟶ L) :
    HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (.up ℤ)).map a) q ≫ cochainLocalSectionUnitAt S q V L =
      cochainLocalSectionUnitAt S q V K ≫
        ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
          (DerivedCategory.Q.map a)).app (op V) := by
  let F := RingedSpace.localAbelianSections S.toRingedSpace
  let E := (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have h₁ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ q).map
      ((F.mapHomologicalComplex (.up ℤ)).map a)) E
  have h₂ := congrArg (fun t ↦ t.app (op V)) ((cochainLocalSectionUnit S q).naturality a)
  have h₂' : E.map (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map a) q) ≫
        ((cochainLocalSectionUnit S q).app L).app (op V) =
      ((cochainLocalSectionUnit S q).app K).app (op V) ≫
        ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
          (DerivedCategory.Q.map a)).app (op V) := h₂
  exact (congrArg (fun t ↦ t ≫ ((cochainLocalSectionUnit S q).app L).app (op V)) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun t ↦
      ((((F.mapHomologicalComplex (.up ℤ)).obj K).sc q).mapHomologyIso E).hom ≫ t) h₂').trans
        (Category.assoc _ _ _).symm))

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem square_unitQ_map {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (I : CochainComplex Z.Modules ℤ) (A : schemeDerivedCategory Z)
    (a : DerivedCategory.Q.obj I ⟶ A) :
    (pushforward f).rightDerivedFunctorUnitQ
        (((pushforward v).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (schemeDerivedDirectImage f).map
        ((pushforward v).rightDerivedFunctorUnitQ I ≫ (schemeDerivedDirectImage v).map a) ≫
      (derivedSquareRightComparison f k g v h).hom.app A =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
        (.up ℤ)).app I) ≫
      (pushforward g).rightDerivedFunctorUnitQ
        (((pushforward k).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (schemeDerivedDirectImage g).map
        ((pushforward k).rightDerivedFunctorUnitQ I ≫ (schemeDerivedDirectImage k).map a) := by
  have hn := (derivedSquareRightComparison f k g v h).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn]
  rw [← Category.assoc, ← Category.assoc]
  rw [Category.assoc _ _ ((derivedSquareRightComparison f k g v h).hom.app _),
    square_unitQ]
  simp only [Functor.map_comp, Category.assoc]

private theorem injective_unit_inverse {Z T : Scheme.{u}} (k : Z ⟶ T)
    (G : Z.Modules) (q : ℕ) (V : T.Opens) (J : InjectiveResolution G) :
    directImageSectionUnitAt k (q : ℤ) V J.cochainComplex ≫
      ((RingedSpace.localHypercohomologyPresheaf T.toRingedSpace (q : ℤ)).map
        ((schemeDerivedDirectImage k).map (inv (DerivedCategory.Q.map J.ι')))).app (op V) =
    (squareInjectiveLocalComparison k G q V J (k ⁻¹ᵁ V) rfl).hom := by
  rw [← injectiveSectionUnit_comparison]
  simp only [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
    IsIso.hom_inv_id, (schemeDerivedDirectImage k).map_id,
    (RingedSpace.localHypercohomologyPresheaf T.toRingedSpace (q : ℤ)).map_id,
    NatTrans.id_app]
  all_goals exact Category.comp_id _

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem square_sections_transport {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (I : CochainComplex Z.Modules ℤ) (V : S.Opens) :
    let e := (NatTrans.mapHomologicalComplex
      (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
        (.up ℤ)).app I
    let hp : v ⁻¹ᵁ (f ⁻¹ᵁ V) = k ⁻¹ᵁ (g ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]
    ((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
      (.up ℤ)).map e =
      eqToHom (congrArg (fun U ↦
        ((RingedSpace.openModuleSections Z.toRingedSpace U).mapHomologicalComplex
          (.up ℤ)).obj I) hp) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.eqToHom_f]
  change ((RingedSpace.openModuleSections S.toRingedSpace V).map
      ((pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom.app
        (I.X n))) = _
  have he : ((RingedSpace.openModuleSections S.toRingedSpace V).map
      ((pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom.app
        (I.X n))) =
      ((RingedSpace.localAbelianSections Z.toRingedSpace).obj (I.X n)).map
        (eqToHom (show k ⁻¹ᵁ (g ⁻¹ᵁ V) = v ⁻¹ᵁ (f ⁻¹ᵁ V) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).op := by
    ext x
    rfl
  rw [he, eqToHom_op, eqToHom_map]

private theorem injectiveComparison_transport {Z T : Scheme.{u}} (k : Z ⟶ T)
    (G : Z.Modules) (q : ℕ) (V : T.Opens) (J : InjectiveResolution G)
    (U : Z.Opens) (hU : U = k ⁻¹ᵁ V) :
    eqToHom (congrArg (fun W ↦
      (((RingedSpace.openModuleSections Z.toRingedSpace W).mapHomologicalComplex
        (.up ℤ)).obj J.cochainComplex).homology (q : ℤ)) hU) ≫
      (squareInjectiveLocalComparison k G q V J (k ⁻¹ᵁ V) rfl).hom =
        (squareInjectiveLocalComparison k G q V J U hU).hom := by
  subst U
  simp only [eqToHom_refl, Category.id_comp]

private theorem squareForward_sections_unit_map {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (I : CochainComplex Z.Modules ℤ) (K : schemeDerivedCategory Z)
    (a : (DerivedCategory.Q (C := SheafOfModules.{u}
      (moduleRings Z.toRingedSpace))).obj I ⟶ K) (q : ℤ) (V : S.Opens) :
    let e := (NatTrans.mapHomologicalComplex
      (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
        (.up ℤ)).app I
    let t := (pushforward k).rightDerivedFunctorUnitQ I ≫ (schemeDerivedDirectImage k).map a
    directImageSectionUnitAt f q V
        (((pushforward v).mapHomologicalComplex (.up ℤ)).obj I) ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
        ((schemeDerivedDirectImage f).map
          ((pushforward v).rightDerivedFunctorUnitQ I ≫ (schemeDerivedDirectImage v).map a) ≫
          (derivedSquareRightComparison f k g v h).hom.app K)).app (op V) =
      HomologicalComplex.homologyMap
          (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
            (.up ℤ)).map e) q ≫
        directImageSectionUnitAt g q V
          (((pushforward k).mapHomologicalComplex (.up ℤ)).obj I) ≫
        ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
          ((schemeDerivedDirectImage g).map t)).app (op V) := by
  dsimp only
  let A := ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
    (((pushforward v).mapHomologicalComplex (.up ℤ)).obj I)
  let B := ((pushforward k).mapHomologicalComplex (.up ℤ)).obj I
  let e := (NatTrans.mapHomologicalComplex
    (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
      (.up ℤ)).app I
  let t := (pushforward k).rightDerivedFunctorUnitQ I ≫ (schemeDerivedDirectImage k).map a
  let H := RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q
  let d := HomologicalComplex.homologyMap
    (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
      (.up ℤ)).map e) q
  have hs := square_unitQ_map f k g v h I K a
  calc
    _ = cochainLocalSectionUnitAt S q V A ≫
        (H.map ((pushforward f).rightDerivedFunctorUnitQ
          (((pushforward v).mapHomologicalComplex (.up ℤ)).obj I) ≫
          (schemeDerivedDirectImage f).map
            ((pushforward v).rightDerivedFunctorUnitQ I ≫
              (schemeDerivedDirectImage v).map a) ≫
          (derivedSquareRightComparison f k g v h).hom.app K)).app (op V) := by
      rw [sections_unitAt]
      simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
      rfl
    _ = cochainLocalSectionUnitAt S q V A ≫
        (H.map (DerivedCategory.Q.map e ≫
          (pushforward g).rightDerivedFunctorUnitQ B ≫
          (schemeDerivedDirectImage g).map t)).app (op V) := by rw [hs]
    _ = d ≫ directImageSectionUnitAt g q V B ≫
        (H.map ((schemeDerivedDirectImage g).map t)).app (op V) := by
      rw [sections_unitAt]
      simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
      have hn := congrArg
        (fun z ↦ z ≫ (H.map ((pushforward g).rightDerivedFunctorUnitQ B)).app (op V) ≫
          (H.map ((schemeDerivedDirectImage g).map t)).app (op V))
        (cochainLocalSectionUnitAt_naturality S q V e).symm
      simp only [Category.assoc] at hn
      convert hn using 1 <;> rfl

private theorem squareForward_injective_transport {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (G : Z.Modules) (J : InjectiveResolution G) (q : ℕ) (V : S.Opens) :
    HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (.up ℤ)).map ((NatTrans.mapHomologicalComplex
            (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
              (.up ℤ)).app J.cochainComplex)) (q : ℤ) ≫
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J
        (k ⁻¹ᵁ (g ⁻¹ᵁ V)) rfl).hom =
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J
        (v ⁻¹ᵁ (f ⁻¹ᵁ V)) (by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).hom := by
  rw [square_sections_transport]
  change (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) (q : ℤ)).map
    (eqToHom _) ≫ _ = _
  rw [eqToHom_map]
  exact injectiveComparison_transport k G q (g ⁻¹ᵁ V) J _ _

private theorem squareSectionUnit_forward_aux {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (G : Z.Modules) (J : InjectiveResolution G) (q : ℕ) (V : S.Opens) :
    let U := f ⁻¹ᵁ V
    let t := (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
       J.cochainComplex ≫
        (schemeDerivedDirectImage v).map (inv (DerivedCategory.Q.map J.ι'))
    directImageSectionUnitAt f (q : ℤ) V
        (((pushforward v).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        ((schemeDerivedDirectImage f).map t ≫
          (derivedSquareRightComparison f k g v h).hom.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInverseOpenComparison g (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) =
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ U) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).hom := by
  dsimp only
  let I := J.cochainComplex
  let B := ((pushforward k).mapHomologicalComplex (.up ℤ)).obj I
  let e := (NatTrans.mapHomologicalComplex
    (pushforwardComp v f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp k g).symm).hom
      (.up ℤ)).app I
  let a := inv (DerivedCategory.Q.map J.ι')
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G
  let t := (pushforward k).rightDerivedFunctorUnitQ I ≫ (schemeDerivedDirectImage k).map a
  let H := RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)
  let H' := RingedSpace.localHypercohomologyPresheaf T.toRingedSpace (q : ℤ)
  let L := (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
    ((schemeDerivedDirectImage k).obj K)).hom.app (op V)
  let C := (squareInverseOpenComparison g (q : ℤ)
    ((schemeDerivedDirectImage k).obj K)).hom.app (op V)
  let d := HomologicalComplex.homologyMap
    (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
      (.up ℤ)).map e) (q : ℤ)
  have hu := sections_to_inverseAt g (q : ℤ) V B
    ((schemeDerivedDirectImage k).obj K) t
  calc
    _ = d ≫ directImageSectionUnitAt g (q : ℤ) V B ≫
        (H.map ((schemeDerivedDirectImage g).map t)).app (op V) ≫ L ≫ C := by
      have hs := squareForward_sections_unit_map f k g v h I K a (q : ℤ) V
      have hh := congrArg (fun z ↦ z ≫ L ≫ C) hs
      simp only [Category.assoc] at hh
      convert hh using 1 <;> rfl
    _ = d ≫ cochainLocalSectionUnitAt T (q : ℤ) (g ⁻¹ᵁ V) B ≫
        (H'.map t).app (op (g ⁻¹ᵁ V)) := by
      exact congrArg (fun z ↦ d ≫ z) hu
    _ = d ≫ (directImageSectionUnitAt k (q : ℤ) (g ⁻¹ᵁ V) I ≫
        (H'.map ((schemeDerivedDirectImage k).map a)).app (op (g ⁻¹ᵁ V))) := by
      rw [sections_unitAt]
      simp only [t, Functor.map_comp, NatTrans.comp_app, Category.assoc]
      rfl
    _ = d ≫ (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J
        (k ⁻¹ᵁ (g ⁻¹ᵁ V)) rfl).hom := by rw [injective_unit_inverse]
    _ = _ := squareForward_injective_transport f k g v h G J q V

end Helpers

/-- The normalized square comparison reaches the raw target endpoint before its
inverse is applied. This is the forward equation needed for cancellation in the
section-unit identity.
Source: Stacks Project, Tags 0D5T and 0D5X
(blueprint: lem-weil-pbc-square-section-unit-forward).

Proof: Resolve the target coefficient by J, use the right-derived mate equation for
the commuting square, and evaluate the universal Leray and inverse-open
factorizations on the same K-injective representative. The resulting map is the
hom of `squareInjectiveLocalComparison` for k. This is the forward half of the
unit cancellation; postcomposition with its inverse gives the parent statement.
The construction is valid for empty opens and identity squares.
-/
theorem squareSectionUnit_forward {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (G : Z.Modules) (J : InjectiveResolution G) (q : ℕ) (V : S.Opens) :
    let U := f ⁻¹ᵁ V
    let t := (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
       J.cochainComplex ≫
        (schemeDerivedDirectImage v).map (inv (DerivedCategory.Q.map J.ι'))
    directImageSectionUnitAt f (q : ℤ) V
        (((pushforward v).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        ((schemeDerivedDirectImage f).map t ≫
          (derivedSquareRightComparison f k g v h).hom.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInverseOpenComparison g (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) =
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ U) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).hom :=
  squareSectionUnit_forward_aux f k g v h G J q V

end AlgebraicGeometry
