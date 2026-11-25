/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
/-! # The derived composition map on an open pullback square -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
/-- The specified composition comparison for an open pullback square.
This abbreviates the existing chosen composition isomorphisms; it adds no data choice.
Source: Stacks Project, Tag 0D5S.
(blueprint: def-pc-open-restricted-composition-map). -/
noncomputable def openRestrictedCompositionMap
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens) (K : schemeDerivedCategory X) :
    (derivedPullback (pullback.snd g' U.ι)).obj ((derivedPullback U.ι).obj K) ⟶
      (derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K) :=
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition))))
    (pullback.snd g' U.ι) U.ι).hom.app K ≫
  eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
    (pullback.condition (f := g') (g := U.ι)).symm) ≫
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition))))
    (pullback.fst g' U.ι) g').inv.app K
end AlgebraicGeometry.SingleComplexBaseChange
