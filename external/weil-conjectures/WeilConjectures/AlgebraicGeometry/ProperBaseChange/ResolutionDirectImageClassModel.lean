/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalClassEdgeMap
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf
import all WeilConjectures.AlgebraicGeometry.Local.LocalHypercohomologyClassUnit
import all WeilConjectures.AlgebraicGeometry.Direct.DirectImageComplexUnit
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ResolutionLerayClassModel
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryLocalClassCycles

/-! # The derived local class on the fixed direct-image model

## References

* Stacks Project, Tags 0BKJ, 0D5X and 079W
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
  AlgebraicGeometry.RingedSpace.topEdgeLocalClass
  AlgebraicGeometry.RingedSpace.topEdgeLocalLeray
  AlgebraicGeometry.RingedSpace.topEdgeDirectImageComparison
namespace AlgebraicGeometry

namespace RingedSpace

variable {Y : RingedSpace.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]

private theorem edge_class_naturality (q : ℤ)
    {K L : DerivedCategory (SheafOfModules.{u} (moduleRings Y))} (a : K ⟶ L) :
    (localHypercohomologyPresheaf Y q).map a ≫ topEdgeLocalClass Y q L =
      topEdgeLocalClass Y q K ≫
        (localAbelianSections Y).map ((DerivedCategory.homologyFunctor _ q).map a) := by
  let P := localHypercohomologyPresheaf Y q
  let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).unit
  let αK := (localHypercohomologySheafificationAt q K).hom
  let αL := (localHypercohomologySheafificationAt q L).hom
  let b := (SheafOfModules.toSheaf (moduleRings Y)).map
    ((DerivedCategory.homologyFunctor _ q).map a)
  have h : U.map (S.map (P.map a)) ≫ U.map αL = U.map αK ≫ U.map b := by
    have hh := congrArg U.map (sheafificationAt_naturality q a)
    change U.map (S.map (P.map a) ≫ αL) = U.map (αK ≫ b) at hh
    simpa only [Functor.map_comp] using hh
  have hu : P.map a ≫ η.app (P.obj L) = η.app (P.obj K) ≫ U.map (S.map (P.map a)) :=
    η.naturality (P.map a)
  unfold topEdgeLocalClass
  change P.map a ≫ (η.app (P.obj L) ≫ U.map αL) =
    (η.app (P.obj K) ≫ U.map αK) ≫ U.map b
  calc
    _ = (P.map a ≫ η.app (P.obj L)) ≫ U.map αL := (Category.assoc _ _ _).symm
    _ = (η.app (P.obj K) ≫ U.map (S.map (P.map a))) ≫ U.map αL :=
      congrArg (fun z ↦ z ≫ U.map αL) hu
    _ = η.app (P.obj K) ≫ (U.map (S.map (P.map a)) ≫ U.map αL) :=
      Category.assoc _ _ _
    _ = η.app (P.obj K) ≫ (U.map αK ≫ U.map b) :=
      congrArg (fun z ↦ η.app (P.obj K) ≫ z) h
    _ = _ := (Category.assoc _ _ _).symm

end RingedSpace

private theorem edge_directImage_localClass
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
    have hl := resolutionLerayClassModel f I K r
    dsimp only at hl
    rw [← localComplexUnit_app_eq] at hl
    have he := (Classical.choose_spec (RingedSpace.unboundedDirectImage_sectionPresheaf f q)).1
    unfold RingedSpace.topEdgeLocalLeray
    dsimp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv]
    rw [show (Classical.choose (RingedSpace.unboundedDirectImage_sectionPresheaf f q)).hom.app K =
      (RingedSpace.localHypercohomologyComparison f q).app K from NatTrans.congr_app he K]
    change b.inv ≫ H.map ((RingedSpace.localLerayComparison f).app K) ≫
      H.map ((RingedSpace.derivedLocalAbelianSections Y).map
        (RingedSpace.topEdgeDirectImageComparison f K).hom) ≫
      H.map ((RingedSpace.derivedLocalAbelianSections Y).map e.hom) = _
    simpa only [cast_eq, b, a, t, RingedSpace.inverseOpenHypercohomologyPresheaf,
      Functor.comp_map, Iso.trans_inv, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ a.inv ≫ H.map z) hl
  have hn := RingedSpace.edge_class_naturality q e.hom
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

private theorem ordinary_class_edge {Y : RingedSpace.{u}}
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) (q : ℤ) :
    (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
        ((((RingedSpace.localAbelianSections Y).mapHomologicalComplex (.up ℤ)).obj I).homology q)
        ≫ (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          (RingedSpace.localSectionComplexSheafificationIso Y q I).hom =
      ShortComplex.leftExactHomologyEdge (RingedSpace.localAbelianSections Y) (I.sc q) := by
  apply (cancel_epi ((I.sc q).map (RingedSpace.localAbelianSections Y)).homologyπ).1
  rw [ShortComplex.homologyπ_leftExactHomologyEdge]
  exact ordinaryLocalClass_cycles I q

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The derived local class becomes the ordinary section edge on the fixed direct-image
complex. -/
theorem resolutionDirectImageClassModel {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (K : schemeDerivedCategory T) :
    let f := g.toLRSHom.toShHom
    let F := RingedSpace.localAbelianSections S.toRingedSpace
    let I := RingedSpace.topEdgeResolution T.toRingedSpace K
    let J := ((RingedSpace.moduleDirectImage f).mapHomologicalComplex (.up ℤ)).obj I
    (RingedSpace.topEdgeInverseModel f q K).inv ≫
        (RingedSpace.topEdgeLocalLeray f q K).inv ≫
        RingedSpace.topEdgeLocalClass S.toRingedSpace q ((schemeDerivedDirectImage g).obj K) ≫
        F.map (localClassDirectImageHomologyIso g q K).hom =
      ShortComplex.leftExactHomologyEdge F (J.sc q) := by
  dsimp only
  have h := edge_directImage_localClass g.toLRSHom.toShHom
    (RingedSpace.topEdgeResolution T.toRingedSpace K) K
    (RingedSpace.topEdgeResolutionIso T.toRingedSpace K).symm q
  exact h.trans (ordinary_class_edge _ q)

end AlgebraicGeometry
