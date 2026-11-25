/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Flat morphisms locally of finite presentation are open

A flat morphism of schemes which is locally of finite presentation is an open map, and so is
every base change of it. This is Mathlib's instance `UniversallyOpen.of_flat` (Stacks `01UA`).
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A flat morphism locally of finite presentation `f : X ⟶ Y` is an open map, and the same holds
after every base change `X ×_Y Y' ⟶ Y'` (Stacks `01UA`).
(blueprint: `lem-weil-pbc-flat-lfp-open`) -/
theorem Flat.isOpenMap_and_isOpenMap_pullback_snd {X Y : Scheme} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] :
    IsOpenMap f.base ∧ ∀ ⦃Y' : Scheme⦄ (g : Y' ⟶ Y), IsOpenMap (pullback.snd f g).base :=
  ⟨f.isOpenMap, fun _ g ↦ (pullback.snd f g).isOpenMap⟩

end AlgebraicGeometry
