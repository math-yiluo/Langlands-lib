/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Named pinned data for the open base-change calculation

Source: Stacks Project, Tags 0D5S and 08HY.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- The exact adjunction family already used by `schemeDerivedBaseChangeMap`.
Its Hom equivalence is pinned to the same left-derived counit and right-derived unit.
This name shares the existing expression and makes no new adjunction choice.
Source: Stacks Project, Tag 08HY, and `exists_schemeDerivedAdjunction`.
(blueprint: def-pc-t2-open-pinned-adjunction). -/
noncomputable abbrev singleComplexOpenPinnedAdjunction
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), derivedPullback f ⊣ schemeDerivedDirectImage f :=
  fun f ↦ Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))

end AlgebraicGeometry
