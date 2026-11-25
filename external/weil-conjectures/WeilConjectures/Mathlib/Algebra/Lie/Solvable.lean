/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Solvable

/-!
# Solvability from the derived algebra, and the radical under isomorphisms

A Lie algebra whose derived algebra `⁅L, L⁆` is solvable is itself solvable. The image of a
solvable ideal under a surjective morphism of Lie algebras is solvable, so the solvable radical is
preserved by isomorphisms; in particular it is a characteristic ideal.

## Main declarations

* `LieIdeal.isSolvable_map`: the image of a solvable ideal under a surjective morphism is
  solvable.
* `LieAlgebra.map_radical`: an isomorphism of Lie algebras maps the radical onto the radical.

## Blueprint

The blueprint subsection `det-d-lie` consists of definitions and facts already in Mathlib:
* `def-wf-lie-algebra`: `LieRing`/`LieAlgebra`, `LieIdeal`, `LieAlgebra.derivedSeries`,
  `LieAlgebra.IsSolvable`, the quotient `L ⧸ I`, `LieModule`, `LieModule.toEnd`;
* `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical`;
* `def-wf-lie-radical-centre`: `LieAlgebra.radical`, `LieAlgebra.center`, and
  `LieAlgebra.HasCentralRadical`; the Killing form is `killingForm`;
* `proposition-lie-algebras-faithful-semisimple-representation--1`: `LieAlgebra.isSolvableAdd`.

`LieAlgebra.map_radical` implements `rem-ptr-wf-lie-radical-centre-3`.
-/

@[expose] public section

namespace LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra whose derived algebra `⁅L, L⁆` is solvable is solvable. -/
theorem isSolvable_of_isSolvable_derivedSeries_one [IsSolvable (derivedSeries R L 1)] :
    IsSolvable L := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable R (derivedSeries R L 1)
  rw [LieIdeal.derivedSeries_eq_bot_iff, derivedSeries_def, ← derivedSeriesOfIdeal_add] at hn
  exact IsSolvable.mk (R := R) (k := n + 1) (by rwa [derivedSeries_def])

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L']

/-- The derived series of an ideal is compatible with images under a surjective morphism. -/
theorem map_derivedSeriesOfIdeal {f : L →ₗ⁅R⁆ L'} (hf : Function.Surjective f) (I : LieIdeal R L)
    (k : ℕ) : (derivedSeriesOfIdeal R L k I).map f = derivedSeriesOfIdeal R L' k (I.map f) := by
  induction k with
  | zero => simp only [derivedSeriesOfIdeal_zero]
  | succ k ih => simp only [derivedSeriesOfIdeal_succ, map_bracket_eq f hf, ih]

/-- The image of a solvable ideal under a surjective morphism of Lie algebras is solvable. -/
theorem isSolvable_map {f : L →ₗ⁅R⁆ L'} (hf : Function.Surjective f) (I : LieIdeal R L)
    [IsSolvable I] : IsSolvable (I.map f) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R I
  rw [derivedSeries_eq_bot_iff] at hk
  refine IsSolvable.mk (R := R) (k := k) ?_
  rw [derivedSeries_eq_bot_iff, ← map_derivedSeriesOfIdeal hf, hk, LieIdeal.map_eq_bot_iff]
  exact bot_le

end LieIdeal

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L']

/-- A surjective morphism of Lie algebras maps the radical into the radical. -/
theorem map_radical_le {f : L →ₗ⁅R⁆ L'} (hf : Function.Surjective f) :
    (radical R L).map f ≤ radical R L' := by
  rw [LieIdeal.map_le_iff_le_comap]
  refine sSup_le fun I (hI : IsSolvable I) ↦ LieIdeal.map_le_iff_le_comap.mp ?_
  exact le_sSup (LieIdeal.isSolvable_map hf I)

/-- **The solvable radical is characteristic.** An isomorphism of Lie algebras `e : L ≃ L'` maps
the radical of `L` onto the radical of `L'`; in particular every automorphism of `L` preserves
its radical.
(blueprint: `rem-ptr-wf-lie-radical-centre-3`) -/
theorem map_radical (e : L ≃ₗ⁅R⁆ L') : (radical R L).map (e : L →ₗ⁅R⁆ L') = radical R L' := by
  refine le_antisymm (map_radical_le e.surjective) fun y hy ↦ ?_
  have h := map_radical_le (R := R) (f := (e.symm : L' →ₗ⁅R⁆ L)) e.symm.surjective
    (LieIdeal.mem_map hy)
  simpa using LieIdeal.mem_map (f := (e : L →ₗ⁅R⁆ L')) h

end LieAlgebra
