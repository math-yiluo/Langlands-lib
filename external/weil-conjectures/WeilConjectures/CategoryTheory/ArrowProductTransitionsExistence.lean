/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The universal-property construction of arrow-indexed product transitions.
(blueprint: lem-weil-pbc-arrow-product-transitions-existence)
Source: Stacks Project, Sites, Tag 0EXZ, construction of canonical transition components.
The proof uses preservation of products by continuous sheaf pushforward and the product
universal property to construct a map with the displayed projection equations. -/
theorem exists_arrow_product_transitions
    {J : Type u} [SmallCategory J]
    (F : J ⥤ Cat.{u, u}) (T : ∀ j : J, GrothendieckTopology (F.obj j))
    [∀ (j k : J) (a : j ⟶ k), (F.map a).toFunctor.IsContinuous (T j) (T k)]
    (A : ∀ j : J, Sheaf (T j) AddCommGrpCat.{u}) :
    let R := fun {j k : J} (a : j ⟶ k) ↦
      (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)
    let B := fun j ↦ ∏ᶜ fun t : Σ k : J, j ⟶ k ↦ (R t.2).obj (A t.1)
    ∃ (q : ∀ {j k : J} (a : j ⟶ k), B j ⟶ (R a).obj (B k)),
      ∀ {j k : J} (a : j ⟶ k) (t : Σ l : J, k ⟶ l),
        q a ≫ (R a).map (Pi.π _ t) =
          Pi.π _ ⟨t.1, a ≫ t.2⟩ ≫
            (Functor.sheafPushforwardContinuousComp'
              (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a t.2).symm))
              AddCommGrpCat.{u} (T j) (T k) (T t.1)).inv.app (A t.1) := by
  sorry
end CategoryTheory
