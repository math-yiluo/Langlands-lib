/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback

/-! # Derived pullback between independent localization universes

Source: Stacks Project, Tags 05RU and 0D5S.
(blueprint: def-pc-derived-pullback-across-universes).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Compare the specified localization with the standard localization of the same complexes.
Source: Stacks Project, Tag 05RU.
(blueprint: def-pc-derived-pullback-across-universes). -/
noncomputable def schemeDerivedStandardEquivalence (X : Scheme.{u})
    [h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    schemeDerivedCategory X ≌
      @schemeDerivedCategory X (HasDerivedCategory.standard _) :=
  Localization.uniq DerivedCategory.Qh
    (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- Transport the standard K-flat derived pullback through localization equivalences.
This constructs a functor even when the two specified derived universes differ.
Source: Stacks Project, Tags 05RU and 06YI.
(blueprint: def-pc-derived-pullback-across-universes). -/
noncomputable def derivedPullbackAcrossUniverses {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hx : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hy : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    schemeDerivedCategory Y ⥤ schemeDerivedCategory X :=
  (schemeDerivedStandardEquivalence Y).functor ⋙
    @derivedPullback X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) ⋙ (schemeDerivedStandardEquivalence X).inverse

end AlgebraicGeometry
