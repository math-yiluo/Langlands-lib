/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf

/-! # The local class of the derived-section unit

## References

* Stacks Project, Cohomology, Tag 01E4, and Tags 0BKJ and 0D5X
-/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
  AlgebraicGeometry.RingedSpace.topEdgeLocalClass
  AlgebraicGeometry.RingedSpace.topEdgeLocalLeray
namespace AlgebraicGeometry
open Scheme.Modules
private theorem quotient_hom_id
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := by rfl

private theorem quotient_inv_id
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).inv.app K = 𝟙 _ := by rfl

@[irreducible] private def localComplexUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h where
  app K := (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
      ((DerivedCategory.quotientCompQhIso C).hom.app K)
  naturality K L f := by
    let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h
    have hn := η.naturality ((HomotopyCategory.quotient C (.up ℤ)).map f)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn ⊢
    rw [(DerivedCategory.quotientCompQhIso D).inv.naturality_assoc]
    erw [reassoc_of% hn]
    simp only [Category.assoc, ← Functor.map_comp]
    erw [(DerivedCategory.quotientCompQhIso C).hom.naturality]

private theorem localComplexUnit_resolution
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {K I : CochainComplex C ℤ} [I.IsKInjective] (s : K ⟶ I) [QuasiIso s] :
    (localComplexUnit F h).app K ≫
        (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h s).hom =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map s) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  have hn := (localComplexUnit F h).naturality s
  dsimp only [Functor.comp_map] at hn
  dsimp only [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Iso.app_inv, asIso_inv]
  rw [← Category.assoc, ← hn]
  simp [localComplexUnit, Category.assoc, ← Functor.map_comp_assoc]

private theorem sheafification_normalization
    {Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (q : ℤ) (I : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ)
    [I.IsKInjective]
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings Y)))
    (r : K ≅ DerivedCategory.Q.obj I) :
    (RingedSpace.localHypercohomologyPresheaf Y q ⋙
        presheafToSheaf (Opens.grothendieckTopology Y)
          AddCommGrpCat.{u}).map r.hom ≫
        (RingedSpace.localHypercohomologySheafificationModel q I).hom =
      (RingedSpace.localHypercohomologySheafificationAt q K).hom ≫
        (DerivedCategory.homologyFunctor.{w, u, u + 1} _ q ⋙
          SheafOfModules.toSheaf.{u} (moduleRings Y)).map r.hom := by
  let C := SheafOfModules.{u} (moduleRings Y)
  let J := (CochainComplex.kInjectiveResolutionFunctor.{u} C).obj
    (DerivedCategory.Q.objPreimage K)
  let s := (CochainComplex.toKInjectiveResolution.{u} C).app
    (DerivedCategory.Q.objPreimage K)
  let : QuasiIso s :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C _).2
  let a : DerivedCategory.Q.obj J ≅ K :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let P := RingedSpace.localHypercohomologyPresheaf Y q ⋙
    presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let G := DerivedCategory.homologyFunctor.{w, u, u + 1} C q ⋙
    SheafOfModules.toSheaf.{u} (moduleRings Y)
  obtain ⟨b, hb⟩ := RingedSpace.exists_complex_map_into_kInjective I J
    (r.inv ≫ a.inv)
  have hn := RingedSpace.sheafificationModel_naturality q b
  change P.map (DerivedCategory.Q.map b) ≫
      (RingedSpace.localHypercohomologySheafificationModel q J).hom =
    (RingedSpace.localHypercohomologySheafificationModel q I).hom ≫
      G.map (DerivedCategory.Q.map b) at hn
  have hh := congrArg (fun z ↦ P.map r.hom ≫ z ≫ G.map (a.hom ≫ r.hom)) hn
  rw [hb] at hh
  simp only [Functor.map_comp, Category.assoc] at hh
  simp only [← P.map_comp_assoc r.hom r.inv, ← G.map_comp_assoc a.inv a.hom,
    Iso.hom_inv_id, Iso.inv_hom_id, P.map_id, G.map_id, Category.id_comp] at hh
  simp only [← G.map_comp r.inv r.hom, Iso.inv_hom_id, G.map_id,
    ] at hh
  change P.map r.hom ≫ (RingedSpace.localHypercohomologySheafificationModel q I).hom =
    (P.map a.inv ≫ (RingedSpace.localHypercohomologySheafificationModel q J).hom ≫
      G.map a.hom) ≫ G.map r.hom
  erw [Category.comp_id] at hh
  simpa only [Category.assoc] using hh.symm

-- Pasting the resolution, homology, and sheafification squares reduces the
-- comparison to cancellation along the homology isomorphism of the resolution.
private theorem sheafification_resolution_diagram
    {C : Type*} [Category C] {A B D E K L M N P Q : C}
    {u : A ⟶ B} {a : B ⟶ D} {b : D ⟶ E} {s : E ⟶ K} [Mono s]
    {v : B ⟶ L} {m : L ⟶ M} {g : D ⟶ M} {h : M ⟶ K}
    {r : L ⟶ N} {p : N ⟶ P} {c : P ⟶ K}
    {t : A ⟶ N} {d : A ⟶ Q} {e : Q ⟶ P} {f : Q ⟶ E}
    (hn : v ≫ m = a ≫ g) (hf : g ≫ h = b ≫ s)
    (hm : m ≫ h = r ≫ p ≫ c) (hu : u ≫ v ≫ r = t)
    (hp : t ≫ p = d ≫ e) (hc : e ≫ c = f ≫ s) :
    u ≫ a ≫ b = d ≫ f := by
  apply (cancel_mono s).1
  simp only [Category.assoc]
  rw [← hf, ← reassoc_of% hn, hm, reassoc_of% hu, reassoc_of% hp, hc]

-- This compares homology in module sheaves, abelian sheaves and abelian presheaves.
private theorem sheafification_unit_of_resolution
    {Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (q : ℤ) (I J : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ)
    [J.IsKInjective] (s : I ⟶ J) [QuasiIso s] :
    let F := RingedSpace.localAbelianSections Y
    let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    let T := SheafOfModules.toSheaf.{u} (moduleRings Y)
    let H := DerivedCategory.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q
    S.map (H.map ((localComplexUnit F
        (RingedSpace.localSectionsEnoughKInjectives Y)).app I)) ≫
        (RingedSpace.localHypercohomologySheafificationAt q (DerivedCategory.Q.obj I)).hom ≫
        T.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app I) =
      S.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        (RingedSpace.localSectionComplexSheafificationIso Y q I).hom := by
  dsimp only
  let F := RingedSpace.localAbelianSections Y
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let T := SheafOfModules.toSheaf.{u} (moduleRings Y)
  let H := DerivedCategory.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q
  let r := asIso (DerivedCategory.Q.map s)
  have hn := sheafification_normalization q J (DerivedCategory.Q.obj I) r
  change S.map (H.map ((RingedSpace.derivedLocalAbelianSections Y).map
      (DerivedCategory.Q.map s))) ≫
      (RingedSpace.localHypercohomologySheafificationModel q J).hom =
    (RingedSpace.localHypercohomologySheafificationAt q (DerivedCategory.Q.obj I)).hom ≫
      T.map ((DerivedCategory.homologyFunctor _ q).map (DerivedCategory.Q.map s)) at hn
  have hc := (RingedSpace.complexSheafificationIso Y q).hom.naturality s
  have hf := (DerivedCategory.homologyFunctorFactors _ q).hom.naturality s
  have hp := (DerivedCategory.homologyFunctorFactors _ q).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map s)
  dsimp only [Functor.comp_map] at hf hp hc
  have hf' := congrArg T.map hf
  have hp' := congrArg S.map hp
  simp only [Functor.map_comp] at hf' hp'
  have hcomp :
      (RingedSpace.derivedLocalAbelianSections Y).map (DerivedCategory.Q.map s) ≫
        (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (RingedSpace.localSectionsEnoughKInjectives Y) (𝟙 J)).hom =
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (RingedSpace.localSectionsEnoughKInjectives Y) s).hom := by
    simp [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso,
      RingedSpace.derivedLocalAbelianSections, F]
  have hu := localComplexUnit_resolution F (RingedSpace.localSectionsEnoughKInjectives Y) s
  rw [← hcomp] at hu
  have hu' := congrArg (fun z ↦ S.map (H.map z)) hu
  simp only [Functor.map_comp] at hu'
  have hm : (RingedSpace.localHypercohomologySheafificationModel q J).hom ≫
      T.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app J) =
    S.map (H.map ((F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
      (RingedSpace.localSectionsEnoughKInjectives Y) (𝟙 J)).hom)) ≫
      S.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)) ≫
      (RingedSpace.localSectionComplexSheafificationIso Y q J).hom := by
    dsimp only [RingedSpace.localHypercohomologySheafificationModel,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
    simp only [Functor.map_comp, Category.assoc]
    erw [((DerivedCategory.homologyFunctorFactors _ q).app J).inv_hom_id_map T,
      Category.comp_id]
  have : Mono (T.map ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).map s)) :=
    inferInstanceAs (Mono (T.map (HomologicalComplex.homologyMap s q)))
  exact sheafification_resolution_diagram hn hf' hm hu' hp' hc

private theorem sheafification_unit
    {Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (q : ℤ) (I : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) :
    let F := RingedSpace.localAbelianSections Y
    let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    let T := SheafOfModules.toSheaf.{u} (moduleRings Y)
    let H := DerivedCategory.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q
    S.map (H.map ((localComplexUnit F
        (RingedSpace.localSectionsEnoughKInjectives Y)).app I)) ≫
        (RingedSpace.localHypercohomologySheafificationAt q (DerivedCategory.Q.obj I)).hom ≫
        T.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app I) =
      S.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        (RingedSpace.localSectionComplexSheafificationIso Y q I).hom := by
  let J := (CochainComplex.kInjectiveResolutionFunctor.{u} _).obj I
  let s := (CochainComplex.toKInjectiveResolution.{u} _).app I
  let : QuasiIso s := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ I).2
  exact sheafification_unit_of_resolution q I J s

private theorem localComplexUnit_class
    {Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (q : ℤ) (I : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) :
    let F := RingedSpace.localAbelianSections Y
    let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    let H := DerivedCategory.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q
    H.map ((localComplexUnit F (RingedSpace.localSectionsEnoughKInjectives Y)).app I) ≫
        RingedSpace.topEdgeLocalClass Y q (DerivedCategory.Q.obj I) ≫
        F.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app I) =
      (DerivedCategory.homologyFunctorFactors _ q).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
          (((F.mapHomologicalComplex (.up ℤ)).obj I).homology q) ≫
        U.map (RingedSpace.localSectionComplexSheafificationIso Y q I).hom := by
  dsimp only
  let F := RingedSpace.localAbelianSections Y
  let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let T := SheafOfModules.toSheaf.{u} (moduleRings Y)
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit
  let H := DerivedCategory.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q
  let a := H.map ((localComplexUnit F (RingedSpace.localSectionsEnoughKInjectives Y)).app I)
  let b := (DerivedCategory.homologyFunctorFactors _ q).hom.app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  have hc := congrArg U.map (sheafification_unit q I)
  change U.map (S.map a ≫
      (RingedSpace.localHypercohomologySheafificationAt q (DerivedCategory.Q.obj I)).hom ≫
      T.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app I)) =
    U.map (S.map b ≫ (RingedSpace.localSectionComplexSheafificationIso Y q I).hom) at hc
  simp only [Functor.map_comp] at hc
  unfold RingedSpace.topEdgeLocalClass
  change a ≫ (η.app _ ≫ U.map _) ≫ U.map _ = b ≫ η.app _ ≫ U.map _
  simp only [Category.assoc]
  have ha : a ≫ η.app _ = η.app _ ≫ U.map (S.map a) := η.naturality a
  have hb : b ≫ η.app _ = η.app _ ≫ U.map (S.map b) := η.naturality b
  erw [reassoc_of% ha, reassoc_of% hb]
  exact congrArg (fun z ↦ η.app _ ≫ z) hc

end AlgebraicGeometry
