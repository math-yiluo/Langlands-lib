/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.CategoryTheory.Filtration

/-!
# Filtrations of objects in an abelian category

Source: Stacks Project, Homology, Definition 12.19.1 (Tag 0121)
(blueprint: def-sp-filtration).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- (blueprint: def-sp-filtration) A decreasing filtration of `A` is an integer-indexed
family of subobjects, decreasing as the integer increases (Stacks, Tag 0121). -/
structure PBCDecreasingFiltration (A : C) where
  step : ℤ → Subobject A
  antitone_step : Antitone step

/-- (blueprint: def-sp-filtration) An object with a decreasing filtration
(Stacks, Tag 0121). -/
structure PBCFilteredObject (C : Type u) [Category.{v} C] [Abelian C] where
  obj : C
  filtration : PBCDecreasingFiltration obj

namespace PBCFilteredObject

/-- (blueprint: def-sp-filtration) A morphism of filtered objects is an underlying morphism
whose restriction to each filtration step factors through the corresponding target step
(Stacks, Tag 0121). -/
structure Hom (A B : PBCFilteredObject C) where
  hom : A.obj ⟶ B.obj
  preserves : ∀ i : ℤ, ∃ lift : (A.filtration.step i : C) ⟶
    (B.filtration.step i : C),
    lift ≫ (B.filtration.step i).arrow = (A.filtration.step i).arrow ≫ hom

/-- (blueprint: def-sp-filtration) Filtered objects and filtration-preserving maps
form the category `Fil(C)` (Stacks, Tag 0121). -/
instance : Category.{v} (PBCFilteredObject C) where
  Hom := Hom
  id A := ⟨𝟙 A.obj, fun i => ⟨𝟙 _, by simp⟩⟩
  comp f g := ⟨f.hom ≫ g.hom, fun i => by
    obtain ⟨f_i, hf_i⟩ := f.preserves i
    obtain ⟨g_i, hg_i⟩ := g.preserves i
    exact ⟨f_i ≫ g_i, by rw [Category.assoc, hg_i, ← Category.assoc, hf_i,
      Category.assoc]⟩⟩
  id_comp := by
    intro A B f
    cases f
    congr 1
    simp
  comp_id := by
    intro A B f
    cases f
    congr 1
    simp
  assoc := by
    intro A B D E f g h
    cases f
    cases g
    cases h
    congr 1
    simp

end PBCFilteredObject

namespace PBCDecreasingFiltration

/-- (blueprint: def-sp-filtration) The filtration induced on a subobject `X` is the
intersection of `X` with each filtration step, viewed inside `X` (Stacks, Tag 0121). -/
noncomputable def induced {A : C} (F : PBCDecreasingFiltration A) (X : Subobject A) :
    PBCDecreasingFiltration (X : C) where
  step i := (Subobject.pullback X.arrow).obj (F.step i)
  antitone_step := by
    intro i j hij
    exact leOfHom ((Subobject.pullback X.arrow).map
      (homOfLE (F.antitone_step hij)))

/-- (blueprint: def-sp-filtration) The filtration on an epimorphic quotient is the
image of each filtration step (Stacks, Tag 0121). -/
noncomputable def quotient {A Y : C} (F : PBCDecreasingFiltration A)
    (π : A ⟶ Y) [Epi π] : PBCDecreasingFiltration Y where
  step i := (Subobject.«exists» π).obj (F.step i)
  antitone_step := by
    intro i j hij
    exact leOfHom ((Subobject.«exists» π).map
      (homOfLE (F.antitone_step hij)))

/-- (blueprint: def-sp-filtration) A filtration is finite when one step is the entire
object and another step is zero (Stacks, Tag 0121). -/
def IsFinite {A : C} (F : PBCDecreasingFiltration A) : Prop :=
  ∃ n m : ℤ, F.step n = ⊤ ∧ F.step m = ⊥

/-- (blueprint: def-sp-filtration) The intersection of the steps exists when there is
a greatest subobject lying in every step (Stacks, Tag 0121). -/
def HasIntersection {A : C} (F : PBCDecreasingFiltration A) : Prop :=
  ∃ X : Subobject A, (∀ i, X ≤ F.step i) ∧
    ∀ Y : Subobject A, (∀ i, Y ≤ F.step i) → Y ≤ X

/-- (blueprint: def-sp-filtration) The union of the steps exists when there is
a least subobject containing every step (Stacks, Tag 0121). -/
def HasUnion {A : C} (F : PBCDecreasingFiltration A) : Prop :=
  ∃ X : Subobject A, (∀ i, F.step i ≤ X) ∧
    ∀ Y : Subobject A, (∀ i, F.step i ≤ Y) → X ≤ Y

/-- (blueprint: def-sp-filtration) A filtration is separated when the greatest
subobject contained in every step is zero (Stacks, Tag 0121). -/
def IsSeparated {A : C} (F : PBCDecreasingFiltration A) : Prop :=
  ∀ X : Subobject A, (∀ i, X ≤ F.step i) → X = ⊥

/-- (blueprint: def-sp-filtration) A filtration is exhaustive when the least
subobject containing every step is the entire object (Stacks, Tag 0121). -/
def IsExhaustive {A : C} (F : PBCDecreasingFiltration A) : Prop :=
  ∀ X : Subobject A, (∀ i, F.step i ≤ X) → X = ⊤

/-- (blueprint: def-sp-filtration) The `n`-th graded piece is the quotient of
`Fⁿ A` by `Fⁿ⁺¹ A` (Stacks, Tag 0121; blueprint node). -/
noncomputable def gradedPiece {A : C} (F : PBCDecreasingFiltration A) (n : ℤ) : C :=
  cokernel (Subobject.ofLE (F.step (n + 1)) (F.step n)
    (F.antitone_step (by omega)))

end PBCDecreasingFiltration

end CategoryTheory
