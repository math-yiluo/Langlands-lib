/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Open restriction of additive derived stalk cohomology

Source: Stacks Project, Tags 0098 and 08DW.
(blueprint: def-pc-open-derived-additive-stalk-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange

/-- The additive derived-stalk comparison for an open subscheme, constructed from
Mathlib's restriction-stalk isomorphism and exact functoriality of localization.

Construction: identify open restriction with restrictFunctor U.ι by overFunctorEquiv.
After forgetting stalk scalars, restrictStalkNatIso identifies the two exact stalk
functors. Apply mapDerivedCategoryNatIso and its composition comparisons. Commute
both exact additive forgetful functors with cohomology by
mapDerivedCategoryHomologyFunctorIso. This constructs the comparison on the entire
derived category, not just on chosen representatives.
Source: Stacks Project, Tags 0098 (stalk restriction) and 08DW (derived restriction).
(blueprint: def-pc-open-derived-additive-stalk-iso). -/
noncomputable def openDerivedAdditiveStalkIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u}) (U : X.Opens) (z : U.toScheme) (i : ℤ) :
    (schemeOpenRestriction X U).mapDerivedCategory ⋙
        comparisonStalkCohomology U.toScheme z i ⋙
          forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk z)) AddCommGrpCat.{u} ≅
      comparisonStalkCohomology X z.val i ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk z.val)) AddCommGrpCat.{u} := by
  let R := schemeOpenRestriction X U
  let L₀ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace z
  let L := RingedSpace.moduleStalkFunctor X.toRingedSpace z.val
  let F₀ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (X.presheaf.stalk z.val)) AddCommGrpCat.{u}
  let := HasDerivedCategory.standard (ModuleCat.{u} (U.toScheme.presheaf.stalk z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk z.val))
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  have : R.Additive := schemeOpenRestriction_additive X U
  have : PreservesFiniteLimits R := schemeOpenRestriction_preservesFiniteLimits X U
  have : PreservesFiniteColimits R := schemeOpenRestriction_preservesFiniteColimits X U
  have : (R ⋙ L₀ ⋙ F₀).Additive := inferInstance
  have : PreservesFiniteLimits (R ⋙ L₀ ⋙ F₀) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (R ⋙ L₀ ⋙ F₀) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (L₀ ⋙ F₀) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (L₀ ⋙ F₀) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (L ⋙ F) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (L ⋙ F) := comp_preservesFiniteColimits _ _
  let α : R ⋙ L₀ ⋙ F₀ ≅ L ⋙ F :=
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (L₀ ⋙ F₀) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι z
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  exact Functor.isoWhiskerLeft R.mapDerivedCategory
      (Functor.isoWhiskerLeft L₀.mapDerivedCategory
        (Functor.mapDerivedCategoryHomologyFunctorIso F₀ i) ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso L₀ F₀) H) ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso R (L₀ ⋙ F₀)) H ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso α) H ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso L F).symm H ≪≫
    Functor.isoWhiskerLeft L.mapDerivedCategory
      (Functor.mapDerivedCategoryHomologyFunctorIso F i).symm

end AlgebraicGeometry
