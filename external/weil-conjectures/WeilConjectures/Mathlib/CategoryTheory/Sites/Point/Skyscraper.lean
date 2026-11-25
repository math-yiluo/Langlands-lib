/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!

# Germs and the skyscraper adjunction

Let `Φ` be a point of a site `(C, J)`. The unit of the adjunction
`CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction` between the fibre
functor on sheaves and the skyscraper sheaf functor is, on the component of a pointed object
`(X, x)` of the site, the germ map of `Φ` at `(X, x)`. This is the form in which the
adjunction is used to compute germs.

## Main results

- `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction_unit_app_hom_app_π`:
  the `x`-th component of the unit of the skyscraper adjunction over `X` is the germ map of
  `Φ` at `(X, x)`.
- `CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive`: the fibre functor on sheaves
  with values in a preadditive category is additive, being a left adjoint.

-/

@[expose] public section

universe w v' u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

/-- The unit of the skyscraper adjunction computes germs: its `x`-th component over `X` is
the germ map of `Φ` at the pointed object `(X, x)`. -/
@[reassoc (attr := simp)]
lemma skyscraperSheafAdjunction_unit_app_hom_app_π (P : Sheaf J A) (X : C)
    (x : Φ.fiber.obj X) :
    (Φ.skyscraperSheafAdjunction.unit.app P).hom.app (op X) ≫
        Pi.π (fun _ : Φ.fiber.obj X ↦ Φ.sheafFiber.obj P) x =
      Φ.toPresheafFiber X x P.obj := by
  have h : (Φ.skyscraperSheafAdjunction.unit.app P).hom =
      Φ.skyscraperPresheafHomEquiv (𝟙 (Φ.sheafFiber.obj P)) := by
    rw [← Adjunction.homEquiv_id]
    exact Φ.skyscraperSheafAdjunction_homEquiv_apply_hom _
  rw [h, skyscraperPresheafHomEquiv_app_π]
  exact Category.comp_id _

/-- The fibre functor on sheaves with values in a preadditive category is additive: being a
left adjoint, it preserves binary coproducts, hence binary biproducts. This is not an instance:
its hypothesis `HasProducts.{w} A` makes instance search get stuck on universe constraints. -/
lemma sheafFiber_additive [Preadditive A] [HasBinaryBiproducts (Sheaf J A)] :
    (Φ.sheafFiber (A := A)).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Φ.sheafFiber (A := A))
  Functor.additive_of_preservesBinaryBiproducts _

end CategoryTheory.GrothendieckTopology.Point
