/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Retraction for derived pullback across localization universes

Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-derived-pullback-across-universes-retraction).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Pullback along a retraction cancels, also between different localization universes.
Source: Stacks Project, Tag 0D5S (composition and identity of derived pullback).
(blueprint: lem-pc-derived-pullback-across-universes-retraction).

Proof: cancel the middle localization equivalence with its counit, mapping this
isomorphism through the standard pullback of i and the inverse equivalence on X.
The composition comparison identifies the successive standard pullbacks with that
of i followed by p. Rewrite this composite as the identity using h. Apply the
identity-pullback comparison, then cancel the remaining equivalence with its unit. -/
theorem derivedPullbackAcrossUniverses_retraction {X Y : Scheme.{u}}
    [hx : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hy : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X) (E : schemeDerivedCategory X) :
    Nonempty ((derivedPullbackAcrossUniverses i).obj
      ((derivedPullbackAcrossUniverses p).obj E) ≅ E) := by
  let d (Z : Scheme.{u}) := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  obtain ⟨_, _, _, comp, _, ident, _⟩ := exists_derivedPullbackComposition (d := d)
  let eX : @schemeDerivedCategory.{u, wX} X hx ≌ @schemeDerivedCategory.{u, u+1} X (d X) :=
    @schemeDerivedStandardEquivalence.{u, wX} X hx
  let eY : @schemeDerivedCategory.{u, wY} Y hy ≌ @schemeDerivedCategory.{u, u+1} Y (d Y) :=
    @schemeDerivedStandardEquivalence.{u, wY} Y hy
  let Li := @derivedPullback X Y i (d Y) (d X)
  let Lp := @derivedPullback Y X p (d X) (d Y)
  change Nonempty (eX.inverse.obj (Li.obj (eY.functor.obj
    (eY.inverse.obj (Lp.obj (eX.functor.obj E))))) ≅ E)
  refine ⟨eX.inverse.mapIso (Li.mapIso (eY.counitIso.app _)) ≪≫
    eX.inverse.mapIso ((comp i p).app (eX.functor.obj E)) ≪≫ ?_⟩
  have hi : @derivedPullback X X (i ≫ p) (d X) (d X) ≅ 𝟭 _ := by
    simpa only [h] using ident X
  exact eX.inverse.mapIso (hi.app (eX.functor.obj E)) ≪≫ (eX.unitIso.app E).symm


end AlgebraicGeometry
