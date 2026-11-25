/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-! # Direct-image normalization on any K-injective representative

Source: Stacks Project, Cohomology, Tag 01E4, lemma-describe-higher-direct-images,
and Tags 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-direct-image-resolution-normalization).
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
-- Normalize two derived functors without unfolding their chosen constructions.
/-- The comparison between the two fixed direct images is normalized on any supplied
K-injective model.
Source: Stacks Project, Tags 079V and 0D5W.
(blueprint: lem-weil-pbc-direct-image-resolution-normalization).

Proof: Lift r.inv followed by the fixed resolution isomorphism to a complex map between
K-injective representatives. Naturality of both resolution comparisons gives the same
map after applying direct image to that lift. This map is invertible since either
comparison is an isomorphism. Cancel it to identify the prescribed direct-image
comparison with the one computed on the supplied model.
-/
theorem directImage_resolution_normalization
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (f : X ⟶ Y) (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    [I.IsKInjective]
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (r : K ≅ DerivedCategory.Q.obj I) :
    let D := RingedSpace.moduleDirectImage f
    letI : D.Additive := RingedSpace.moduleDirectImage_additive f
    (RingedSpace.topEdgeDirectImageComparison f K).hom ≫
        D.rightDerivedFunctor.map r.hom ≫ (D.rightDerivedFunctorObjQIso I).hom =
      (RingedSpace.sectionDerivedDirectImage f).map r.hom ≫
        (D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)).hom := by
  dsimp only
  let D := RingedSpace.moduleDirectImage f
  let : D.Additive := RingedSpace.moduleDirectImage_additive f
  let R := RingedSpace.sectionDerivedDirectImage f
  let R' := D.rightDerivedFunctor
  let J := RingedSpace.topEdgeResolution X K
  let e := RingedSpace.topEdgeResolutionIso X K
  let a := R.mapIso r ≪≫ D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)
  let a' := R'.mapIso r ≪≫ D.rightDerivedFunctorObjQIso I
  let c := R.mapIso e.symm ≪≫ D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 J)
  let c' := R'.mapIso e.symm ≪≫ D.rightDerivedFunctorObjQIso J
  obtain ⟨b, hb⟩ := RingedSpace.exists_complex_map_into_kInjective I J (r.inv ≫ e.inv)
  let t := DerivedCategory.Q.map ((D.mapHomologicalComplex (.up ℤ)).map b)
  have ha : a.hom ≫ t = c.hom := by
    have hh := RingedSpace.resolutionObjIso_naturality D
      (RingedSpace.localSectionsEnoughKInjectives X) b
    change R.map (DerivedCategory.Q.map b) ≫
        (D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 J)).hom =
      (D.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)).hom ≫ t at hh
    change (R.map r.hom ≫ _) ≫ t = R.map e.inv ≫ _
    rw [Category.assoc, ← hh, ← R.map_comp_assoc, hb]
    simp only [Iso.hom_inv_id_assoc]
  have ha' : a'.hom ≫ t = c'.hom := by
    have hh := D.rightDerivedFunctor_map_Q_map_comp_objQIso_hom b
    change (R'.map r.hom ≫ _) ≫ t = R'.map e.inv ≫ _
    rw [Category.assoc, ← hh, ← R'.map_comp_assoc, hb]
    simp only [Iso.hom_inv_id_assoc]
  have : IsIso (a'.hom ≫ t) := by rw [ha']; infer_instance
  have : IsIso t := IsIso.of_isIso_comp_left a'.hom t
  have hc : c.hom ≫ c'.inv ≫ a'.hom = a.hom := by
    apply (cancel_mono t).1
    rw [Category.assoc, Category.assoc, ha', ha]
    erw [Iso.inv_hom_id, Category.comp_id]
  simpa only [RingedSpace.topEdgeDirectImageComparison, c, c', a, a', R, R', D, J, e,
    RingedSpace.derivedModuleDirectImage, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc] using hc

end AlgebraicGeometry
