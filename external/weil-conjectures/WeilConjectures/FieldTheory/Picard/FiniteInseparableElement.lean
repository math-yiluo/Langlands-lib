/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FieldTheory.Picard.FieldTower
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# An inseparable element in a finite nonseparable field extension

Source: Stacks Project, Algebra, Definition 10.42.1 (Tag 030O), applied to a finite extension
(blueprint: lem-pc-finite-inseparable-element).
-/

@[expose] public section

universe u v

namespace FieldExtension

/-- (blueprint: lem-pc-finite-inseparable-element) A finite field extension that is not
separable has an element whose minimal polynomial is inseparable.

For the contrapositive, assume every element has a separable minimal polynomial. Each
finitely generated intermediate field is finite-dimensional over the base, hence algebraic.
Its elements remain separable over the base. The empty transcendence basis therefore makes
each such field separably generated. By Definition 10.42.1 (Tag 030O), the whole extension
is separable, contrary to the hypothesis. -/
theorem exists_not_isSeparable_of_not_isSeparableExtension
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfinite : degree k K ≠ ⊤) (hnot : ¬ Algebra.IsSeparableExtension k K) :
    ∃ α : K, ¬ IsSeparable k α := by
  classical
  have : Module.Finite k K := by
    by_contra hf
    exact hfinite (by simp [degree, hf])
  by_contra h
  push Not at h
  apply hnot
  have : Algebra.IsSeparable k K := ⟨h⟩
  intro F _
  refine ⟨∅, ?_, ?_⟩
  · refine ⟨algebraicIndependent_empty_type_iff.mpr (algebraMap k F).injective, ?_⟩
    intro s hs _
    have : IsEmpty s := hs.isEmpty_of_isAlgebraic
    simpa only [Set.range_eq_empty] using (Set.isEmpty_coe_sort.mp this).symm
  · exact Algebra.isSeparable_tower_top_of_isSeparable k _ F

end FieldExtension
