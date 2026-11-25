/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Elements
public import WeilConjectures.Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Points of a site at a larger universe

The fibre functor of a point `Φ : J.Point.{w}` of a site takes values in `Type w`, and the
statements about points that involve a coefficient category `A` require `A` to be concrete
over that same `Type w`. This file lifts a point to any larger universe: `Φ.ulift` is the
point of `J` at `Type (max w w')` whose fibre functor is `Φ.fiber ⋙ uliftFunctor`.

Since the category of elements of `Φ.fiber ⋙ uliftFunctor` is equivalent to that of
`Φ.fiber`, nothing changes: the fibre functors of `Φ.ulift` and of `Φ` on presheaves and on
sheaves with values in `A` are isomorphic.

## Main definitions

- `CategoryTheory.GrothendieckTopology.Point.ulift`: the point `Φ.ulift : J.Point.{max w w'}`
  attached to a point `Φ : J.Point.{w}`.
- `CategoryTheory.GrothendieckTopology.Point.uliftPresheafFiberIso`,
  `CategoryTheory.GrothendieckTopology.Point.uliftSheafFiberIso`: the fibre functors of
  `Φ.ulift` on `A`-valued presheaves and sheaves agree with those of `Φ`.
-/

@[expose] public section

universe w' w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

variable (Φ : Point.{w} J)

/-- A point of a site whose fibre functor takes values in `Type w` may be seen as a point
whose fibre functor takes values in `Type (max w w')`, by composing with `uliftFunctor`
(blueprint `lemma-openclosed-point-ulift`). -/
@[simps fiber]
noncomputable def ulift : Point.{max w w'} J where
  fiber := Φ.fiber ⋙ uliftFunctor.{w', w}
  isCofiltered := .of_equivalence (Functor.Elements.uliftEquivalence.{w'} Φ.fiber).symm
  initiallySmall :=
    have : InitiallySmall.{max w w'} Φ.fiber.Elements := initiallySmall_lift.{w', w} _
    initiallySmall_of_initial_of_initiallySmall
      (Functor.Elements.uliftEquivalence.{w'} Φ.fiber).inverse
  jointly_surjective _ hR x := by
    obtain ⟨Y, f, hf, y, hy⟩ := Φ.jointly_surjective _ hR x.down
    exact ⟨Y, f, hf, ULift.up y, ULift.ext hy⟩

@[simp]
lemma ulift_fiber_map {X Y : C} (f : X ⟶ Y) (x : (Φ.ulift.{w'}).fiber.obj X) :
    (Φ.ulift.{w'}).fiber.map f x = ULift.up (Φ.fiber.map f x.down) :=
  rfl

variable (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{max w w', max w w'} A]

-- the colimits needed by `Φ.presheafFiber` exist as soon as those needed by
-- `(Φ.ulift).presheafFiber` do
local instance : HasColimitsOfSize.{w, w} A := hasColimitsOfSizeShrink.{w, w, w', w'} A

/-- Taking the fibre of an `A`-valued presheaf at a point of a site does not depend on the
universe in which the fibre functor of the point is considered. -/
noncomputable def uliftPresheafFiberIso :
    (Φ.ulift.{w'}).presheafFiber (A := A) ≅ Φ.presheafFiber (A := A) :=
  have : (Functor.Elements.uliftEquivalence.{w'} Φ.fiber).functor.Initial :=
    Functor.initial_of_adjunction (Functor.Elements.uliftEquivalence.{w'} Φ.fiber).toAdjunction
  have : HasColimitsOfShape (Φ.fiber ⋙ uliftFunctor.{w', w}).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (Φ.ulift.{w'}).fiber.Elementsᵒᵖ A)
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π Φ.fiber).op)
    (Functor.Final.colimIso (Functor.Elements.uliftEquivalence.{w'} Φ.fiber).functor.op)

/-- Taking the fibre of an `A`-valued sheaf at a point of a site does not depend on the
universe in which the fibre functor of the point is considered
(blueprint `lemma-openclosed-point-ulift`). -/
noncomputable def uliftSheafFiberIso :
    (Φ.ulift.{w'}).sheafFiber (A := A) ≅ Φ.sheafFiber (A := A) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (Φ.uliftPresheafFiberIso A)

end GrothendieckTopology.Point

end CategoryTheory
