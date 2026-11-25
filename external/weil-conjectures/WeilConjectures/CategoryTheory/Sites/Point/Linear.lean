/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!

# The fibre functors at a point are linear

Let `Φ` be a point of a site and let `A` be an `R`-linear category. The fibre functor
`Φ.presheafFiber` on `A`-valued presheaves is a colimit of evaluation functors, and so
commutes with multiplication of morphisms by scalars; so does the fibre functor
`Φ.sheafFiber` on sheaves.

## Main results

- `CategoryTheory.GrothendieckTopology.Point.presheafFiber_map_smul` and
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber_map_smul`: `(r • g)_Φ = r • g_Φ`.

## Implementation notes

These belong next to the definition of the fibre functors in
`Mathlib.CategoryTheory.Sites.Point.Basic`; they are kept in a separate file because the
project's companion file of that Mathlib file is imported by almost the whole project.
-/

@[expose] public section

universe w v' u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {R : Type*} [Semiring R] {A : Type u'} [Category.{v'} A] [Preadditive A] [Linear R A]
  [HasColimitsOfSize.{w, w} A]

/-- The fibre functor on presheaves commutes with scalar multiplication of morphisms. -/
lemma presheafFiber_map_smul {P Q : Cᵒᵖ ⥤ A} (r : R) (g : P ⟶ Q) :
    Φ.presheafFiber.map (r • g) = r • Φ.presheafFiber.map g := by
  ext X x
  rw [toPresheafFiber_naturality, Linear.comp_smul, toPresheafFiber_naturality,
    NatTrans.app_smul, Linear.smul_comp]

/-- The fibre functor on sheaves commutes with scalar multiplication of morphisms. -/
lemma sheafFiber_map_smul {P Q : Sheaf J A} (r : R) (g : P ⟶ Q) :
    Φ.sheafFiber.map (r • g) = r • Φ.sheafFiber.map g :=
  Φ.presheafFiber_map_smul r g.hom

end CategoryTheory.GrothendieckTopology.Point
