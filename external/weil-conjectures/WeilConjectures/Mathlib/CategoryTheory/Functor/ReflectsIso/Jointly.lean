/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# A pair of functors which jointly reflects isomorphisms

`CategoryTheory.JointlyReflectIsomorphisms` is stated for a family of functors
`F i : C ⥤ D i` whose target category is allowed to depend on the index `i`. The case of a
pair of functors `F₁ : C ⥤ D₁` and `F₂ : C ⥤ D₂` with *different* targets therefore needs a
genuinely dependent two-element family; this file provides it, indexed by `Bool` with `true`
carrying `F₁` and `false` carrying `F₂`.

## Main definitions

- `CategoryTheory.pairFunctor`: the two-element family of functors given by `F₁` and `F₂`.

## Main results

- `CategoryTheory.jointlyReflectIsomorphisms_pairFunctor`: two functors jointly reflect
  isomorphisms as soon as every morphism they both send to an isomorphism is an isomorphism.
- `CategoryTheory.JointlyReflectIsomorphisms.isIso_of_pairFunctor`: the converse, in the
  two-hypothesis form a human caller wants.
- `CategoryTheory.JointlyReflectIsomorphisms.of_iso` and
  `CategoryTheory.JointlyReflectIsomorphisms.pairFunctor_of_iso`: joint reflection of
  isomorphisms is invariant under replacing the functors by isomorphic ones.

-/

@[expose] public section

universe v₁ v u₁ u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D₁ D₂ : Type u₁} [Category.{v₁} D₁] [Category.{v₁} D₂]

/-- The two-element family of categories with value `D₁` at `true` and `D₂` at `false`.

This is a `scoped instance`: its head is `cond b D₁ D₂` with `D₁` and `D₂` implicit, so as a
global instance it would be tried on every goal of that shape and then have to solve two
side goals. -/
scoped instance instCategoryCond (b : Bool) : Category.{v₁} (cond b D₁ D₂) :=
  Bool.rec (motive := fun b ↦ Category.{v₁} (cond b D₁ D₂)) ‹Category D₂› ‹Category D₁› b

/-- A family of functors isomorphic to a family which jointly reflects isomorphisms jointly
reflects isomorphisms. -/
lemma JointlyReflectIsomorphisms.of_iso {I : Type*} {D : I → Type*} [∀ i, Category (D i)]
    {F G : ∀ i, C ⥤ D i} (hF : JointlyReflectIsomorphisms F) (e : ∀ i, F i ≅ G i) :
    JointlyReflectIsomorphisms G where
  isIso f _ := (hF.isIso_iff f).2 fun i ↦ (NatIso.isIso_map_iff (e i) f).2 inferInstance

variable (F₁ : C ⥤ D₁) (F₂ : C ⥤ D₂)

/-- The two-element family of functors with value `F₁ : C ⥤ D₁` at `true` and `F₂ : C ⥤ D₂`
at `false`. This is the shape in which a pair of functors is fed to
`CategoryTheory.JointlyReflectIsomorphisms` and to the lemmas about it.

The index type is `Bool` and the family of target categories is `fun b ↦ cond b D₁ D₂`,
rather than `Fin 2` with a `Matrix.cons` or a `Sum`: `cond` is the eliminator of `Bool`, so
`cond true D₁ D₂` and `cond false D₁ D₂` reduce to `D₁` and `D₂` by `rfl`, and every
statement about the family therefore splits into two goals about `F₁` and `F₂` with no
transport. -/
def pairFunctor (b : Bool) : C ⥤ cond b D₁ D₂ :=
  Bool.rec (motive := fun b ↦ C ⥤ cond b D₁ D₂) F₂ F₁ b

@[simp]
lemma pairFunctor_true : pairFunctor F₁ F₂ true = F₁ := rfl

@[simp]
lemma pairFunctor_false : pairFunctor F₁ F₂ false = F₂ := rfl

/-- Two functors jointly reflect isomorphisms as soon as every morphism which both of them
send to an isomorphism is an isomorphism. -/
lemma jointlyReflectIsomorphisms_pairFunctor
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), IsIso (F₁.map f) → IsIso (F₂.map f) → IsIso f) :
    JointlyReflectIsomorphisms (pairFunctor F₁ F₂) where
  isIso f :=
    h f (inferInstanceAs (IsIso ((pairFunctor F₁ F₂ true).map f)))
      (inferInstanceAs (IsIso ((pairFunctor F₁ F₂ false).map f)))

variable {F₁ F₂}

/-- The two-hypothesis form of `CategoryTheory.JointlyReflectIsomorphisms` for a pair of
functors: a morphism sent to an isomorphism by both `F₁` and `F₂` is an isomorphism. -/
lemma JointlyReflectIsomorphisms.isIso_of_pairFunctor
    (hP : JointlyReflectIsomorphisms (pairFunctor F₁ F₂)) {X Y : C} (f : X ⟶ Y)
    (h₁ : IsIso (F₁.map f)) (h₂ : IsIso (F₂.map f)) : IsIso f :=
  (hP.isIso_iff f).2 fun b ↦ by
    cases b
    exacts [h₂, h₁]

/-- A pair of functors isomorphic to a pair which jointly reflects isomorphisms jointly
reflects isomorphisms. -/
lemma JointlyReflectIsomorphisms.pairFunctor_of_iso
    (hP : JointlyReflectIsomorphisms (pairFunctor F₁ F₂)) {G₁ : C ⥤ D₁} {G₂ : C ⥤ D₂}
    (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂) : JointlyReflectIsomorphisms (pairFunctor G₁ G₂) :=
  hP.of_iso fun b ↦ by
    cases b
    exacts [e₂, e₁]

end CategoryTheory
