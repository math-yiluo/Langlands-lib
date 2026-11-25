/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse

/-! # Canonical tensor shifts on schemes
Source: Stacks Project, Tag 06YH, total tensor localization.
(blueprint: def-sc-scheme-canonical-tensor-shift).
-/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
/-- Canonical Koszul tensor shifts, with independent localization universe.
Source: Stacks Tag 06YH (blueprint: def-sc-scheme-canonical-tensor-shift). -/
@[instance_reducible]
noncomputable def schemeCanonicalTensorShift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    (curriedTensor (schemeDerivedCategory X)).CommShift₂Int := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact DerivedCategory.commShift₂CurriedTensor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))

end AlgebraicGeometry
