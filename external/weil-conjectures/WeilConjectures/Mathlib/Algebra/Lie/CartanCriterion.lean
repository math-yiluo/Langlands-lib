/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import WeilConjectures.Mathlib.Algebra.Lie.Engel
public import WeilConjectures.Mathlib.Algebra.Lie.Solvable

/-!
# Cartan's criteria for Lie algebras of endomorphisms

This file states Cartan's trace criterion for a Lie algebra of endomorphisms of a
finite-dimensional vector space, and the non-degeneracy of the Killing form of a Lie algebra with
trivial radical, in the forms used by the blueprint.

## Main declarations

* `LieSubalgebra.isSolvable_of_trace_mul_eq_zero`: **Cartan's trace criterion**: a Lie algebra
  `A` of endomorphisms with `tr (X Y) = 0` for all `X ∈ ⁅A, A⁆` and `Y ∈ A` is solvable.
* `LieAlgebra.HasTrivialRadical.killingForm_nondegenerate`: the Killing form of a
  finite-dimensional characteristic-zero Lie algebra with trivial radical is non-degenerate.
* `LieAlgebra.HasTrivialRadical.derivedSeries_eq_top`: a finite-dimensional characteristic-zero
  Lie algebra with trivial radical is perfect, `⁅L, L⁆ = L`.

## Blueprint

* `LieSubalgebra.isSolvable_of_trace_mul_eq_zero` implements `lemma-cartan-s-criterion--1`.
* `LieAlgebra.HasTrivialRadical.killingForm_nondegenerate` implements
  `lemma-killing--1`.
* `LieAlgebra.HasTrivialRadical.killingForm_nondegenerate` and
  `LieAlgebra.HasTrivialRadical.derivedSeries_eq_top` together implement `lemma-killing`.
-/

@[expose] public section

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {k M : Type*} [Field k] [CharZero k] [AddCommGroup M] [Module k M]
  [FiniteDimensional k M]

/-- **Cartan's trace criterion.** Let `A` be a Lie algebra of endomorphisms of a
finite-dimensional vector space `M` over a field of characteristic zero. If `tr (X Y) = 0` for all
`X ∈ ⁅A, A⁆` and `Y ∈ A`, then `A` is solvable.
(blueprint: `lemma-cartan-s-criterion--1`) -/
theorem isSolvable_of_trace_mul_eq_zero (A : LieSubalgebra k (Module.End k M))
    (h : ∀ X ∈ derivedSeries k A 1, ∀ Y : A,
      LinearMap.trace k M ((X : Module.End k M) * Y) = 0) :
    IsSolvable A := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton A := inferInstance
    infer_instance
  set D := derivedSeries k A 1
  have hD : traceForm k D M = 0 := by
    ext X Y
    exact h X X.2 Y
  have hDD := isNilpotent_derivedSeries_of_traceForm_eq_zero hD
  set DD := derivedSeries k D 1
  have hS : LieRing.IsNilpotent (toEnd k DD M).range := by
    refine ((toEnd k DD M).range.exists_forall_apply_eq_zero_and_isNilpotent ?_).2
    rintro _ ⟨X, rfl⟩
    exact isNilpotent_toEnd_of_isNilpotent k DD M X
  have : IsSolvable DD := Function.Injective.lieAlgebra_isSolvable
    (f := (toEnd k DD M).rangeRestrict) fun X Y hXY ↦ by
      have hXY := Subtype.ext_iff.mp hXY
      exact Subtype.ext <| Subtype.ext <| Subtype.ext hXY
  have : IsSolvable D := isSolvable_of_isSolvable_derivedSeries_one (R := k)
  exact isSolvable_of_isSolvable_derivedSeries_one (R := k)

end LieSubalgebra

namespace LieAlgebra.HasTrivialRadical

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [Module.Finite k L]

/-- The Killing form of a finite-dimensional Lie algebra with trivial radical over a field of
characteristic zero is non-degenerate. This is Cartan's criterion for semisimplicity,
`LieAlgebra.HasTrivialRadical.instIsKilling`.
(blueprint: `lemma-killing--1`) -/
theorem killingForm_nondegenerate [HasTrivialRadical k L] : (killingForm k L).Nondegenerate :=
  IsKilling.killingForm_nondegenerate k L

/-- A finite-dimensional Lie algebra with trivial radical over a field of characteristic zero is
perfect: `⁅L, L⁆ = L`. The Killing complement of `⁅L, L⁆` is an ideal meeting `⁅L, L⁆` trivially,
so it is central; the centre lies in the radical, which is zero. Together with
`LieAlgebra.HasTrivialRadical.killingForm_nondegenerate` this is the blueprint lemma
`lemma-killing`. -/
theorem derivedSeries_eq_top [HasTrivialRadical k L] : derivedSeries k L 1 = ⊤ := by
  set D := derivedSeries k L 1
  have hc := D.isCompl_killingCompl
  have hD : D.killingCompl ≤ center k L := fun z hz ↦ by
    refine (mem_maxTrivSubmodule k L L z).mpr fun x ↦ ?_
    have hx : ⁅x, z⁆ ∈ D := by
      have hD : D = ⁅(⊤ : LieIdeal k L), ⊤⁆ := by
        simp only [D, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
      rw [hD]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top z)
    have h : ⁅x, z⁆ ∈ D ⊓ D.killingCompl := ⟨hx, lie_mem_right k L _ x z hz⟩
    rwa [hc.inf_eq_bot, LieSubmodule.mem_bot] at h
  have hZ : center k L = ⊥ := by
    rw [eq_bot_iff, ← HasTrivialRadical.radical_eq_bot (R := k) (L := L)]
    exact center_le_radical k L
  have hD : D.killingCompl = ⊥ := le_bot_iff.mp (hD.trans hZ.le)
  have := hc.sup_eq_top
  rwa [hD, sup_bot_eq] at this

end LieAlgebra.HasTrivialRadical
