/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
import all WeilConjectures.AlgebraicGeometry.Direct.DirectImageComplexUnit
import all WeilConjectures.AlgebraicGeometry.Local.LocalHypercohomologyClassUnit
import WeilConjectures.AlgebraicGeometry.Direct.DirectImageResolutionNormalization
import WeilConjectures.AlgebraicGeometry.Square.SquareLocalClassNaturality

/-! # The local direct-image class on an integer complex

Source: Stacks Project, Cohomology, Tag 01E4, lemma-describe-higher-direct-images,
and Tags 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-direct-image-integer-local-class).
-/

@[expose] public section
set_option autoImplicit false
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
  AlgebraicGeometry.RingedSpace.topEdgeDirectImageComparison
namespace AlgebraicGeometry
open Scheme.Modules
private theorem directImage_leray_model
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (f : X ⟶ Y) (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    [I.IsKInjective]
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (r : K ≅ DerivedCategory.Q.obj I) :
    let D := RingedSpace.moduleDirectImage f
    letI : D.Additive := RingedSpace.moduleDirectImage_additive f
    let F := RingedSpace.localAbelianSections Y
    let P := D ⋙ F
    let R := P.rightDerivedFunctorOfQuasiIsoResolutions
      (RingedSpace.localSectionsEnoughKInjectives X)
    let c := R.mapIso r ≪≫ P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
      (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)
    let e := D.rightDerivedFunctor.mapIso r ≪≫ D.rightDerivedFunctorObjQIso I
    c.inv ≫ (RingedSpace.localLerayComparison f).app K ≫
        (RingedSpace.derivedLocalAbelianSections Y).map
          ((RingedSpace.topEdgeDirectImageComparison f K).hom ≫ e.hom) =
      (localComplexUnit F (RingedSpace.localSectionsEnoughKInjectives Y)).app
        ((D.mapHomologicalComplex (.up ℤ)).obj I) := by
  dsimp only
  let D := RingedSpace.moduleDirectImage f
  let : D.Additive := RingedSpace.moduleDirectImage_additive f
  let F := RingedSpace.localAbelianSections Y
  let P := D ⋙ F
  let R := P.rightDerivedFunctorOfQuasiIsoResolutions
    (RingedSpace.localSectionsEnoughKInjectives X)
  let RF := RingedSpace.derivedLocalAbelianSections Y
  let c := P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)
  let d := D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)
  have he := directImage_resolution_normalization f I K r
  have hn := (RingedSpace.localLerayComparison f).naturality r.hom
  dsimp only [Functor.comp_map] at hn
  have hu : (localComplexUnit P (RingedSpace.localSectionsEnoughKInjectives X)).app I =
      c.inv := by
    apply (cancel_mono c.hom).1
    rw [Iso.inv_hom_id]
    have hh := localComplexUnit_resolution P
      (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)
    erw [CategoryTheory.Functor.map_id] at hh
    exact hh
  change (c.inv ≫ R.map r.inv) ≫ (RingedSpace.localLerayComparison f).app K ≫
      RF.map ((RingedSpace.topEdgeDirectImageComparison f K).hom ≫
        D.rightDerivedFunctor.map r.hom ≫ (D.rightDerivedFunctorObjQIso I).hom) = _
  erw [he, RF.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hn]
  erw [← R.map_comp_assoc r.inv r.hom, Iso.inv_hom_id, R.map_id, Category.id_comp]
  rw [← hu]
  simpa only [localComplexUnit_app_eq, cast_eq] using directImage_complex_unit f I

/-- The derived direct-image local class is ordinary sheafification on a K-injective
integer complex, with the specified resolution and Leray normalizations.
Source: Stacks Project, Tags 01E4, 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-direct-image-integer-local-class).

Proof: Evaluate the universal factorization defining the Leray transformation at the
complex, and cancel the direct-image derived unit. Compare the two direct-image
functors by a map between K-injective models; naturality of their resolution
isomorphisms identifies the comparison on the given model. Transport by the supplied
isomorphism from the derived object. Taking homology identifies the Leray comparison
with the derived-section unit. Naturality of the local class and its unit calculation
then cancel all resolution factors and leave the ordinary sheafification class.
-/
theorem directImage_integer_localClass
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (f : X ⟶ Y) (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    [I.IsKInjective]
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (r : K ≅ DerivedCategory.Q.obj I) (q : ℤ) :
    let D := RingedSpace.moduleDirectImage f
    letI : D.Additive := RingedSpace.moduleDirectImage_additive f
    let F := RingedSpace.localAbelianSections Y
    let P := D ⋙ F
    let J := (D.mapHomologicalComplex (.up ℤ)).obj I
    let b := (RingedSpace.inverseOpenHypercohomologyPresheaf f q).mapIso r ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso
        (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)) ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _
    let d := (DerivedCategory.homologyFunctor _ q).mapIso
        (D.rightDerivedFunctor.mapIso r ≪≫ D.rightDerivedFunctorObjQIso I) ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app J
    b.inv ≫ (RingedSpace.topEdgeLocalLeray f q K).inv ≫
        RingedSpace.topEdgeLocalClass Y q ((RingedSpace.derivedModuleDirectImage f).obj K) ≫
        F.map d.hom =
      (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
          (((F.mapHomologicalComplex (.up ℤ)).obj J).homology q) ≫
        (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          (RingedSpace.localSectionComplexSheafificationIso Y q J).hom := by
  dsimp only
  let D := RingedSpace.moduleDirectImage f
  let : D.Additive := RingedSpace.moduleDirectImage_additive f
  let F := RingedSpace.localAbelianSections Y
  let P := D ⋙ F
  let H := DerivedCategory.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) q
  let J := (D.mapHomologicalComplex (.up ℤ)).obj I
  let e := D.rightDerivedFunctor.mapIso r ≪≫ D.rightDerivedFunctorObjQIso I
  let b := (RingedSpace.inverseOpenHypercohomologyPresheaf f q).mapIso r ≪≫
    H.mapIso (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
      (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _
  let a := (DerivedCategory.homologyFunctorFactors _ q).app
    ((P.mapHomologicalComplex (.up ℤ)).obj I)
  let t := H.map ((localComplexUnit F
    (RingedSpace.localSectionsEnoughKInjectives Y)).app J)
  have hb : b.inv ≫ (RingedSpace.topEdgeLocalLeray f q K).inv ≫
        (RingedSpace.localHypercohomologyPresheaf Y q).map e.hom = a.inv ≫ t := by
    have hl := directImage_leray_model f I K r
    have he := (Classical.choose_spec (RingedSpace.unboundedDirectImage_sectionPresheaf f q)).1
    unfold RingedSpace.topEdgeLocalLeray
    dsimp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv]
    rw [show (Classical.choose (RingedSpace.unboundedDirectImage_sectionPresheaf f q)).hom.app K =
      (RingedSpace.localHypercohomologyComparison f q).app K from NatTrans.congr_app he K]
    change b.inv ≫ H.map ((RingedSpace.localLerayComparison f).app K) ≫
      H.map ((RingedSpace.derivedLocalAbelianSections Y).map
        (RingedSpace.topEdgeDirectImageComparison f K).hom) ≫
      H.map ((RingedSpace.derivedLocalAbelianSections Y).map e.hom) = _
    simpa only [b, a, t, RingedSpace.inverseOpenHypercohomologyPresheaf,
      Functor.comp_map, Iso.trans_inv, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ a.inv ≫ H.map z) hl
  have hn := RingedSpace.squareLocalClass_naturality q e.hom
  have hu := localComplexUnit_class q J
  change b.inv ≫ (RingedSpace.topEdgeLocalLeray f q K).inv ≫
      RingedSpace.topEdgeLocalClass Y q ((RingedSpace.derivedModuleDirectImage f).obj K) ≫
      F.map ((DerivedCategory.homologyFunctor _ q).map e.hom ≫
        (DerivedCategory.homologyFunctorFactors _ q).hom.app J) = _
  rw [F.map_comp]
  erw [← reassoc_of% hn]
  have hh := congrArg (fun z ↦ z ≫
    RingedSpace.topEdgeLocalClass Y q (DerivedCategory.Q.obj J) ≫
    F.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app J)) hb
  calc
    _ = (a.inv ≫ t) ≫ RingedSpace.topEdgeLocalClass Y q (DerivedCategory.Q.obj J) ≫
        F.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app J) := by
      simpa only [Category.assoc, RingedSpace.localHypercohomologyPresheaf,
        Functor.comp_map] using hh
    _ = _ := by
      have hc := congrArg (fun z ↦ a.inv ≫ z) hu
      change a.inv ≫ (t ≫ RingedSpace.topEdgeLocalClass Y q (DerivedCategory.Q.obj J) ≫
          F.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app J)) =
        a.inv ≫ (a.hom ≫ _) at hc
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hc

end AlgebraicGeometry
