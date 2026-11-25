/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# The morphism of presheaves of rings attached to a morphism of schemes

This file spells out the morphism of the underlying presheaves of rings of a morphism of
schemes in the shape expected by `PresheafOfModules.pullback` and
`PresheafOfModules.pushforward`, namely as a morphism
`Y.sheaf.obj ⋙ forget₂ _ _ ⟶ ((Opens.map f.base).op ⋙ X.sheaf.obj) ⋙ forget₂ _ _`.
It is the morphism underlying `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`.

## Main declarations

- `AlgebraicGeometry.Scheme.Hom.toRingCatPresheafHom`

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- The morphism of the underlying presheaves of rings of a morphism of schemes, spelled in
the shape expected by the pullback and pushforward functors on presheaves of modules. This is
the morphism underlying `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`. -/
def Hom.toRingCatPresheafHom (f : X ⟶ Y) :
    Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u} ⟶
      ((Opens.map f.base).op ⋙ X.sheaf.obj) ⋙ forget₂ CommRingCat RingCat.{u} :=
  Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)

@[simp]
lemma Hom.toRingCatSheafHom_hom (f : X ⟶ Y) :
    f.toRingCatSheafHom.hom = f.toRingCatPresheafHom := rfl

end AlgebraicGeometry.Scheme
