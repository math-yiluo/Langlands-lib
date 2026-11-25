/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Cohomological delta-functors

Source: Stacks Project, Homology, Definitions 010Q, 010R, 010S
(blueprint: def-weil-pbc-delta-functor).

## Main definitions

* `CategoryTheory.CohomologicalDeltaFunctor`: additive functors with connecting maps,
  exactness, and naturality for short exact sequences.
* `CategoryTheory.CohomologicalDeltaFunctor.Hom`: compatible natural transformations.
* `CategoryTheory.CohomologicalDeltaFunctor.IsUniversal`: unique extension from degree zero.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- A cohomological delta-functor consists of additive functors in nonnegative degrees and
connecting maps indexed by short exact sequences, including their arrows. The initial map is
monic. Exactness at each of the three repeating positions is expressed using Mathlib's
`ShortComplex.Exact`; the witnessing zero composites are part of the exactness assertions.
The final field is naturality in a morphism of short exact sequences.
Stacks Project, Homology, Definition 010Q (blueprint: def-weil-pbc-delta-functor). -/
structure CohomologicalDeltaFunctor (A : Type u₁) (B : Type u₂)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B] where
  F : ℕ → A ⥤ B
  additive : ∀ n : ℕ, (F n).Additive
  delta : ∀ (S : ShortComplex A), S.ShortExact →
    ∀ n : ℕ, (F n).obj S.X₃ ⟶ (F (n + 1)).obj S.X₁
  mono_zero : ∀ (S : ShortComplex A) (_hS : S.ShortExact), Mono ((F 0).map S.f)
  exact_middle : ∀ (S : ShortComplex A) (_hS : S.ShortExact) (n : ℕ),
    ∃ h : (F n).map S.f ≫ (F n).map S.g = 0,
      (ShortComplex.mk ((F n).map S.f) ((F n).map S.g) h).Exact
  exact_right : ∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
    ∃ h : (F n).map S.g ≫ delta S hS n = 0,
      (ShortComplex.mk ((F n).map S.g) (delta S hS n) h).Exact
  exact_left : ∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
    ∃ h : delta S hS n ≫ (F (n + 1)).map S.f = 0,
      (ShortComplex.mk (delta S hS n) ((F (n + 1)).map S.f) h).Exact
  naturality : ∀ (S T : ShortComplex A) (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ),
      delta S hS n ≫ (F (n + 1)).map φ.τ₁ =
        (F n).map φ.τ₃ ≫ delta T hT n

namespace CohomologicalDeltaFunctor

/-- A morphism of cohomological delta-functors is a natural transformation in each degree
whose components commute with every connecting map.
Stacks Project, Homology, Definition 010R (blueprint: def-weil-pbc-delta-functor). -/
structure Hom {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    (F G : CohomologicalDeltaFunctor A B) where
  app : ∀ n : ℕ, F.F n ⟶ G.F n
  naturality : ∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
    F.delta S hS n ≫ (app (n + 1)).app S.X₁ =
      (app n).app S.X₃ ≫ G.delta S hS n

/-- Universality means every natural transformation in degree zero extends to a unique
morphism of cohomological delta-functors.
Stacks Project, Homology, Definition 010S (blueprint: def-weil-pbc-delta-functor). -/
def IsUniversal {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B) : Prop :=
  ∀ (G : CohomologicalDeltaFunctor A B) (t : F.F 0 ⟶ G.F 0),
    ∃! φ : Hom F G, φ.app 0 = t

end CohomologicalDeltaFunctor
end CategoryTheory
