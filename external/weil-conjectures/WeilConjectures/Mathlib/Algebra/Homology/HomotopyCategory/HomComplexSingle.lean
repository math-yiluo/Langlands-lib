/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Cohomology classes out of a single complex

For an object `P` and a cochain complex `L`, the cohomology classes of degree `n` from `P[0]`
to `L` vanish if and only if every morphism `P ⟶ L^n` killed by the differential factors
through the differential `L^{n-1} ⟶ L^n`
(`CochainComplex.subsingleton_cohomologyClass_singleFunctor_iff`).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

open HomComplex in
/-- For an object `P`, the cohomology classes of degree `n` from `P[0]` to `L` vanish
if and only if every morphism `P ⟶ L^n` killed by the differential factors through the
differential `L^{n-1} ⟶ L^n`. -/
lemma subsingleton_cohomologyClass_singleFunctor_iff (P : C) (L : CochainComplex C ℤ) (n : ℤ) :
    Subsingleton (CohomologyClass ((singleFunctor C 0).obj P) L n) ↔
      ∀ f : P ⟶ L.X n, f ≫ L.d n (n + 1) = 0 → ∃ g : P ⟶ L.X (n - 1), g ≫ L.d (n - 1) n = f := by
  refine ⟨fun h f hf ↦ ?_, fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  · refine (Cocycle.fromSingleMk_mem_coboundaries_iff f (zero_add n) (n + 1) rfl hf (n - 1)
      (by lia)).1 ?_
    rw [← CohomologyClass.mk_eq_zero_iff]
    exact Subsingleton.elim _ _
  · suffices H : ∀ a : CohomologyClass ((singleFunctor C 0).obj P) L n, a = 0 by rw [H a, H b]
    intro a
    obtain ⟨x, rfl⟩ := a.mk_surjective
    obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (zero_add n) (n + 1) rfl
    rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff f (zero_add n)
      (n + 1) rfl hf (n - 1) (by lia)]
    exact h f hf

end CochainComplex
