/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category

/-!

# Isomorphisms of points of a site

A morphism of points of a site `(C, J)` is a morphism of the fibre functors in the opposite
direction (`CategoryTheory.GrothendieckTopology.Point.Hom`). Consequently an isomorphism of
the fibre functors is the same thing as an isomorphism of points, and an isomorphism of
points induces an isomorphism of the fibre functors on `A`-valued sheaves.

## Main definitions

- `CategoryTheory.GrothendieckTopology.Point.isoMk`: an isomorphism of the fibre functors
  of two points of a site is an isomorphism of the points.
- `CategoryTheory.GrothendieckTopology.Point.sheafFiberIso`: the isomorphism of the fibre
  functors on sheaves induced by an isomorphism of points, described on germs by
  `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app`.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

/-- An isomorphism between the fibre functors of two points of a site is an isomorphism
between the points. Note that morphisms of points go in the direction opposite to the
morphisms of the fibre functors, so the two components are swapped. -/
@[simps]
def isoMk {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁.fiber ≅ Φ₂.fiber) : Φ₁ ≅ Φ₂ where
  hom := ⟨e.inv⟩
  inv := ⟨e.hom⟩

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- An isomorphism of points of a site induces an isomorphism of the fibre functors on
`A`-valued sheaves, by functoriality of
`CategoryTheory.GrothendieckTopology.Point.Hom.sheafFiber`. -/
@[simps]
noncomputable def sheafFiberIso {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    Φ₁.sheafFiber (A := A) ≅ Φ₂.sheafFiber where
  hom := e.inv.sheafFiber
  inv := e.hom.sheafFiber
  hom_inv_id := by rw [← Hom.sheafFiber_comp, e.hom_inv_id, Hom.sheafFiber_id]
  inv_hom_id := by rw [← Hom.sheafFiber_comp, e.inv_hom_id, Hom.sheafFiber_id]

/-- The germ description of
`CategoryTheory.GrothendieckTopology.Point.sheafFiberIso`: on the germ at a pointed object
`(X, x)` of the site, the isomorphism induced by an isomorphism `e` of points is the germ
map at the transported point `e.hom.hom.app X x`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_sheafFiberIso_inv_app {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂)
    (P : Sheaf J A) (X : C) (x : Φ₂.fiber.obj X) :
    Φ₂.toPresheafFiber X x P.obj ≫ (sheafFiberIso e (A := A)).inv.app P =
      Φ₁.toPresheafFiber X (e.hom.hom.app X x) P.obj := by
  simp [sheafFiberIso]

end GrothendieckTopology.Point

end CategoryTheory
