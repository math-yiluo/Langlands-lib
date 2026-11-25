/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Precoverage

/-! # Finite indexed covering axioms

Source: Stacks Project, Sites, Definition 00VH and Lemma 09YL.
(blueprint: def-weil-pbc-finite-precoverage)
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.Precoverage

variable {C : Type u} [Category.{v} C]

/-- Stability under base change for finite indexed covering families.
Source: Stacks Project, Sites, Definition 00VH axiom (3), restricted to the finite
covering families of Situation 0A34. Repetitions are allowed, but the index is finite.
(blueprint: def-weil-pbc-finite-precoverage) -/
class IsStableUnderFiniteBaseChange (J : Precoverage C) : Prop where
  mem_coverings_of_isPullback {ι : Type (max u v)} [Finite ι]
    {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (hR : Presieve.ofArrows X f ∈ J S) {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    Presieve.ofArrows P p₁ ∈ J Y

/-- Stability under composition for finite indexed covering families.
Source: Stacks Project, Sites, Definition 00VH axiom (2), restricted to the finite
covering families of Situation 0A34. Both the outer and each inner index are finite.
(blueprint: def-weil-pbc-finite-precoverage) -/
class IsStableUnderFiniteComposition (J : Precoverage C) : Prop where
  comp_mem_coverings {ι : Type (max u v)} [Finite ι]
    {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ J S)
    {σ : ι → Type (max u v)} [∀ i, Finite (σ i)] {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ J (X i)) :
    Presieve.ofArrows (fun p : Σ i, σ i ↦ Y _ p.2) (fun _ ↦ g _ _ ≫ f _) ∈ J S

/-- The unrestricted base-change axiom implies its finite-index restriction.
Source: the definition of `Precoverage.IsStableUnderBaseChange`.
Proof: apply the unrestricted axiom to the given finite family.
(blueprint: def-weil-pbc-finite-precoverage) -/
instance finiteBaseChange_of_baseChange (J : Precoverage C) [J.IsStableUnderBaseChange] :
    J.IsStableUnderFiniteBaseChange where
  mem_coverings_of_isPullback := Precoverage.mem_coverings_of_isPullback

/-- The unrestricted composition axiom implies its finite-index restriction.
Source: the definition of `Precoverage.IsStableUnderComposition`.
Proof: apply the unrestricted axiom to the given finite families.
(blueprint: def-weil-pbc-finite-precoverage) -/
instance finiteComposition_of_composition (J : Precoverage C) [J.IsStableUnderComposition] :
    J.IsStableUnderFiniteComposition where
  comp_mem_coverings := by
    exact fun {ι} [Finite ι] {S} {X} f hf {σ} [∀ i, Finite (σ i)] {Y} g hg =>
      Precoverage.IsStableUnderComposition.comp_mem_coverings f hf g hg

end CategoryTheory.Precoverage
