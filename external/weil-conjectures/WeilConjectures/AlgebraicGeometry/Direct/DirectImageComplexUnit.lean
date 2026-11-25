/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.Local.LocalHypercohomologyClassUnit

/-! # The unit equation for the local Leray comparison

Source: Stacks Project, Cohomology, Tag 01E4, lemma-describe-higher-direct-images,
and Tags 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-direct-image-complex-unit).
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
private theorem localComplexUnit_app_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (I : CochainComplex C ℤ) :
    (localComplexUnit F h).app I =
      (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
        ((HomotopyCategory.quotient C (.up ℤ)).obj I) := by
  unfold localComplexUnit
  dsimp only
  erw [quotient_inv_id, Category.id_comp, quotient_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

private theorem resolution_identity_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (I : CochainComplex C ℤ) [I.IsKInjective]
    [IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I))] :
    (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)).hom =
      inv ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
        ((HomotopyCategory.quotient C (.up ℤ)).obj I)) := by
  dsimp only [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    asIso_hom, asIso_inv]
  erw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id,
    Iso.app_hom, quotient_hom_id,
    Category.id_comp, Category.id_comp, Category.comp_id]

-- The unit equation crosses three derived categories and their quotient comparisons.
private theorem leray_complex_unit
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (f : X ⟶ Y) (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    [I.IsKInjective] :
    let D := RingedSpace.moduleDirectImage f
    letI : D.Additive := RingedSpace.moduleDirectImage_additive f
    let F := RingedSpace.localAbelianSections Y
    (localComplexUnit (D ⋙ F) (RingedSpace.localSectionsEnoughKInjectives X)).app I ≫
        (RingedSpace.localLerayComparison f).app (DerivedCategory.Q.obj I) ≫
        (RingedSpace.derivedLocalAbelianSections Y).map
          (D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
            (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)).hom =
      (localComplexUnit F (RingedSpace.localSectionsEnoughKInjectives Y)).app
        ((D.mapHomologicalComplex (.up ℤ)).obj I) := by
  dsimp only
  let D := RingedSpace.moduleDirectImage f
  let : D.Additive := RingedSpace.moduleDirectImage_additive f
  let F := RingedSpace.localAbelianSections Y
  let P := D ⋙ F
  let RD := D.rightDerivedFunctorOfQuasiIsoResolutions
    (RingedSpace.localSectionsEnoughKInjectives X)
  let RF := RingedSpace.derivedLocalAbelianSections Y
  let RP := P.rightDerivedFunctorOfQuasiIsoResolutions
    (RingedSpace.localSectionsEnoughKInjectives X)
  let π := HomotopyCategory.quotient (SheafOfModules.{u} (moduleRings X)) (.up ℤ)
  let ηD := D.rightDerivedFunctorOfQuasiIsoResolutionsUnit
    (RingedSpace.localSectionsEnoughKInjectives X)
  let ηP := P.rightDerivedFunctorOfQuasiIsoResolutionsUnit
    (RingedSpace.localSectionsEnoughKInjectives X)
  let e := DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings X))
  have hfac := NatTrans.congr_app (Classical.choose_spec
    ((Functor.rightDerivedFunctorOfQuasiIsoResolutions_universal P
      (RingedSpace.localSectionsEnoughKInjectives X)
      (RingedSpace.sectionDerivedDirectImage f ⋙ RF)).surjective
        (RingedSpace.localLerayCompositeUnit f))) (π.obj I)
  change ηP.app (π.obj I) ≫
      (RingedSpace.localLerayComparison f).app (DerivedCategory.Qh.obj (π.obj I)) =
    (RingedSpace.localLerayCompositeUnit f).app (π.obj I) at hfac
  have := D.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso
    (RingedSpace.localSectionsEnoughKInjectives X) I
  erw [localComplexUnit_app_eq, localComplexUnit_app_eq, resolution_identity_hom]
  erw [← Category.assoc (ηP.app _) ((RingedSpace.localLerayComparison f).app _) _, hfac]
  dsimp only [RingedSpace.localLerayCompositeUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  erw [← RF.map_comp (ηD.app (π.obj I)) (inv (ηD.app (π.obj I))),
    IsIso.hom_inv_id, RF.map_id, Category.comp_id]
  have hc : DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl P) (.up ℤ)).inv.app
        (π.obj I)) = 𝟙 _ := by
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl P) (.up ℤ)).inv.app I)) = _
    have he : (Functor.mapHomologicalComplexCompIso (Iso.refl P) (.up ℤ)).inv.app I =
        𝟙 _ := by ext n; rfl
    rw [he, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp only [Functor.mapHomotopyCategory_obj, π, HomotopyCategory.quotient_obj_as]
  erw [hc, Category.id_comp]
  simp only [Functor.mapHomotopyCategory_obj, π, HomotopyCategory.quotient_obj_as]

/-- The local Leray comparison factors the direct-image derived unit through the
section derived unit on the direct-image complex.
Source: Stacks Project, Tags 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-direct-image-complex-unit).

Proof: Evaluate the universal factorization defining the Leray transformation at the
homotopy class of I. On a K-injective complex the direct-image derived unit is
invertible. The recorded resolution comparison for the identity is its inverse.
Cancel these two maps. The quotient-composition comparisons are identity maps,
so the remaining factor is precisely the section derived unit.
-/
theorem directImage_complex_unit
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (f : X ⟶ Y) (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    [I.IsKInjective] :
    let D := RingedSpace.moduleDirectImage f
    letI : D.Additive := RingedSpace.moduleDirectImage_additive f
    let F := RingedSpace.localAbelianSections Y
    (cast (by rfl) (((D ⋙ F).rightDerivedFunctorOfQuasiIsoResolutionsUnit.{w}
      (RingedSpace.localSectionsEnoughKInjectives X)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) :
      DerivedCategory.Q.obj (((D ⋙ F).mapHomologicalComplex (.up ℤ)).obj I) ⟶ _) ≫
        (RingedSpace.localLerayComparison f).app (DerivedCategory.Q.obj I) ≫
        (RingedSpace.derivedLocalAbelianSections Y).map
          (D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
            (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)).hom =
      cast (by rfl) ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit.{w}
        (RingedSpace.localSectionsEnoughKInjectives Y)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((D.mapHomologicalComplex (.up ℤ)).obj I))) := by
  simpa only [localComplexUnit_app_eq, cast_eq] using leray_complex_unit f I

end AlgebraicGeometry
