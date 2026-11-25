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
import all WeilConjectures.AlgebraicGeometry.Direct.DirectImageComplexUnit
import WeilConjectures.AlgebraicGeometry.Direct.DirectImageResolutionNormalization

/-! # The Leray comparison on a supplied K-injective model

## References

* Stacks Project, Tags 0D5W, 0D5X and 079V
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

/-- On a supplied K-injective model, the inverse composite-resolution comparison,
Leray comparison, and direct-image comparison give the ordinary derived-section unit. -/
theorem resolutionLerayClassModel
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
      cast (by rfl) ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit.{w}
        (RingedSpace.localSectionsEnoughKInjectives Y)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((D.mapHomologicalComplex (.up ℤ)).obj I))) := by
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

end AlgebraicGeometry
