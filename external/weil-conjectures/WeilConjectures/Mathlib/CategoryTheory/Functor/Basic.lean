/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Iterating an endofunctor

For an endofunctor `G : C ⥤ C` and a natural number `n`, this file defines the `n`-fold
composition `G.iterate n : C ⥤ C`.

## Main definitions

- `CategoryTheory.Functor.iterate`: the `n`-fold composition of an endofunctor, with
  `G.iterate 0 = 𝟭 C` and `G.iterate (n + 1) = G.iterate n ⋙ G`.

## Implementation notes

Unlike `Nat.iterate`, whose definitional unfolding is `f^[n + 1] = f^[n] ∘ f`, the recursion
here applies the new copy of `G` last: `G.iterate (n + 1) = G.iterate n ⋙ G`, that is
`Gⁿ⁺¹ = G ∘ Gⁿ`. This makes iterated structure maps of algebras, such as
`CategoryTheory.Endofunctor.IsoAlgebra.strIterate`, definitional. Accordingly, the
definitional equation is `Functor.iterate_succ'`, matching `Function.iterate_succ'`, and the
other order is the lemma `Functor.iterate_succ`, matching `Function.iterate_succ`. Since
composition of functors is definitionally associative, both hold as equalities of functors.

The file also records that equal composites stay equal under a functor
(`CategoryTheory.Functor.map_comp_map_eq_map_comp_map`,
`CategoryTheory.Functor.map_comp_map_comp_map_comp_eq`), in forms suited to rewriting.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C]

/-- The `n`-fold composition of an endofunctor, with `G.iterate 0 = 𝟭 C` and
`G.iterate (n + 1) = G.iterate n ⋙ G`. -/
def iterate (G : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => G.iterate n ⋙ G

variable (G : C ⥤ C)

@[simp]
lemma iterate_zero : G.iterate 0 = 𝟭 C :=
  rfl

lemma iterate_succ (n : ℕ) : G.iterate (n + 1) = G.iterate n ⋙ G :=
  rfl

lemma iterate_succ' (n : ℕ) : G.iterate (n + 1) = G.iterate n ⋙ G :=
  rfl


@[simp]
lemma iterate_one : G.iterate 1 = G :=
  rfl

lemma iterate_succ_left (n : ℕ) : G.iterate (n + 1) = G ⋙ G.iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G.iterate (n + 1) ⋙ G = G ⋙ G.iterate n ⋙ G
    rw [ih]
    rfl


lemma iterate_add (m n : ℕ) : G.iterate (m + n) = G.iterate m ⋙ G.iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G.iterate (m + n) ⋙ G = G.iterate m ⋙ G.iterate n ⋙ G
    rw [ih]
    rfl

end CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- Two equal composites stay equal under a functor. -/
lemma map_comp_map_eq_map_comp_map
    {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A B B' C : 𝒞} {f₁ : A ⟶ B} {f₂ : B ⟶ C} {g₁ : A ⟶ B'} {g₂ : B' ⟶ C}
    (w : f₁ ≫ f₂ = g₁ ≫ g₂) : G.map f₁ ≫ G.map f₂ = G.map g₁ ≫ G.map g₂ := by
  rw [← G.map_comp, w, G.map_comp]

/-- Two equal composites stay equal under a functor, followed by a common morphism. -/
lemma map_comp_map_comp_map_comp_eq
    {ℬ 𝒞 𝒟 : Type*} [Category* ℬ] [Category* 𝒞] [Category* 𝒟]
    (R : ℬ ⥤ 𝒞) (G : 𝒞 ⥤ 𝒟) {A B C B' : 𝒞} {L : ℬ} {E : 𝒟} {a : A ⟶ B} {b : B ⟶ C}
    {c : C ⟶ R.obj L} {x : A ⟶ B'} {y : B' ⟶ R.obj L} (d : (R ⋙ G).obj L ⟶ E)
    (w : x ≫ y = a ≫ b ≫ c) :
    G.map a ≫ G.map b ≫ G.map c ≫ d = G.map x ≫ G.map y ≫ d := by
  simpa using congrArg (fun f ↦ G.map f ≫ d) w.symm

end CategoryTheory.Functor
