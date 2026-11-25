/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Adjunctions between linear functors

If one of the two functors of an adjunction between `R`-linear categories is `R`-linear,
so is the other. These are the `R`-linear analogues of
`CategoryTheory.Adjunction.right_adjoint_additive` and
`CategoryTheory.Adjunction.left_adjoint_additive`.

The lift of an `R`-linear functor to a full subcategory is `R`-linear
(`CategoryTheory.ObjectProperty.lift_linear`).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Adjunction

open CategoryTheory.Functor

variable {R : Type*} [Semiring R] {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
  [Category.{v₂} D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

/-- The right adjoint of an `R`-linear functor is `R`-linear. -/
lemma right_adjoint_linear [F.Linear R] : G.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).symm.injective
    (by simp [homEquiv_counit, Linear.smul_comp, Linear.comp_smul])

/-- The left adjoint of an `R`-linear functor is `R`-linear. -/
lemma left_adjoint_linear [G.Linear R] : F.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).injective
    (by simp [homEquiv_unit, Linear.smul_comp, Linear.comp_smul])

end CategoryTheory.Adjunction

namespace CategoryTheory.ObjectProperty

variable (R : Type*) [Semiring R] {C D : Type*} [Category* C] [Category* D] [Preadditive C]
  [Preadditive D] [Linear R C] [Linear R D] (P : ObjectProperty D) (F : C ⥤ D)
  (hF : ∀ X, P (F.obj X))

/-- The lift of an `R`-linear functor to a full subcategory is `R`-linear. -/
instance lift_linear [F.Linear R] : (P.lift F hF).Linear R where
  map_smul f r := P.fullyFaithfulι.map_injective (F.map_smul r f)

end CategoryTheory.ObjectProperty
