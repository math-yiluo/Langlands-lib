/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The set of arrows as a functor on categories

Source: Stacks Project, Sites, proof of Tag 09YL
(blueprint: def-weil-pbc-arrows-functor).

## Main definitions

* `CategoryTheory.Cat.arrows`: the set-valued functor of all arrows.

## Main statements

* `CategoryTheory.Cat.arrows_map_id`: identity preserves every arrow.
* `CategoryTheory.Cat.arrows_map_comp`: composition acts by successive arrow maps.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Cat

/-- Source: Stacks Project, Sites, proof of Tag 09YL
(blueprint: def-weil-pbc-arrows-functor). The identity functor acts identically on arrows.
Proof: write an arrow as its source, target and morphism; the identity preserves all three. -/
theorem arrows_map_id (C : Cat.{v, u}) :
    (fun a : Arrow C ↦ Arrow.mk ((𝟭 C).map a.hom)) = id := by
  funext a
  simp

/-- Source: Stacks Project, Sites, proof of Tag 09YL
(blueprint: def-weil-pbc-arrows-functor). Composition acts by successive arrow maps.
Proof: the two expressions have the same source and target and the same morphism,
by the definition of functor composition. -/
theorem arrows_map_comp {C D E : Cat.{v, u}} (f : C ⟶ D) (g : D ⟶ E) :
    (fun a : Arrow C ↦ Arrow.mk ((f ≫ g).toFunctor.map a.hom)) =
      (fun a : Arrow D ↦ Arrow.mk (g.toFunctor.map a.hom)) ∘
        (fun a : Arrow C ↦ Arrow.mk (f.toFunctor.map a.hom)) := by
  funext a
  rfl

/-- Source: Stacks Project, Sites, proof of Tag 09YL
(blueprint: def-weil-pbc-arrows-functor). A category is sent to the set of all its arrows,
and a functor sends an arrow to its image, including its source and target. -/
def arrows : Cat.{v, u} ⥤ Type (max u v) where
  obj C := Arrow C
  map f := ↾fun a ↦ Arrow.mk (f.toFunctor.map a.hom)
  map_id C := congrArg (fun f ↦ TypeCat.ofHom f) (arrows_map_id C)
  map_comp f g := congrArg (fun f ↦ TypeCat.ofHom f) (arrows_map_comp f g)

end CategoryTheory.Cat
