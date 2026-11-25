/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Named pinned data for the open base-change calculation

Source: Stacks Project, Tags 0D5S and 08HY.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- The exact composition family already used by `schemeDerivedBaseChangeMap`.
This name shares the pinned expression; it does not select new comparison data.
Source: Stacks Project, Tag 0D5S, and `exists_derivedPullbackComposition`.
(blueprint: def-pc-t2-open-pinned-composition). -/
noncomputable abbrev singleComplexOpenPinnedComposition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
  @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))

end AlgebraicGeometry
