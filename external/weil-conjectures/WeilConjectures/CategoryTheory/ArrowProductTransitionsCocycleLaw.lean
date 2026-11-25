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

/-- Canonical product transitions satisfying their cocycle law once their projections
are known. (blueprint: lem-weil-pbc-arrow-product-transitions-cocycle-law)
Source: Stacks Project, Sites, Tag 0EXZ. Proof by testing both sides after every product
projection, using naturality of the composition comparison and associativity. -/
theorem arrow_product_transitions_cocycle_of_projections
    {J : Type u} [SmallCategory J]
    (F : J ⥤ Cat.{u, u}) (T : ∀ j : J, GrothendieckTopology (F.obj j))
    [∀ (j k : J) (a : j ⟶ k), (F.map a).toFunctor.IsContinuous (T j) (T k)]
    (A : ∀ j : J, Sheaf (T j) AddCommGrpCat.{u}) :
    let R := fun {j k : J} (a : j ⟶ k) ↦
      (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)
    let B := fun j ↦ ∏ᶜ fun t : Σ k : J, j ⟶ k ↦ (R t.2).obj (A t.1)
    ∀ (q : ∀ {j k : J} (a : j ⟶ k), B j ⟶ (R a).obj (B k)),
      (∀ {j k : J} (a : j ⟶ k) (t : Σ l : J, k ⟶ l),
        q a ≫ (R a).map (Pi.π _ t) =
          Pi.π _ ⟨t.1, a ≫ t.2⟩ ≫
            (Functor.sheafPushforwardContinuousComp'
              (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a t.2).symm))
              AddCommGrpCat.{u} (T j) (T k) (T t.1)).inv.app (A t.1)) →
      ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
        q (a ≫ b) = q a ≫ (R a).map (q b) ≫
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm))
            AddCommGrpCat.{u} (T j) (T k) (T l)).hom.app (B l) := by
  sorry
end CategoryTheory
