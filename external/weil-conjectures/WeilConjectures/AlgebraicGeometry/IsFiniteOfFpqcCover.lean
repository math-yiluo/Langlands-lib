/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Finiteness descends along fpqc covering families

Source: Stacks Project, Descent, Lemma Tag 02LA, descent direction of Definition Tag 02KO
(blueprint: lem-weil-pbc-fpqc-descend-finite).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finiteness descends along an fpqc covering family.
Source: Stacks Project, Descent, Lemma Tag 02LA and Definition Tag 02KO
(blueprint: lem-weil-pbc-fpqc-descend-finite).

Proof:
1. Use the source library's proved descent of finiteness along surjective flat
   quasi-compact morphisms (Tag 02LA).
2. The given fpqc precover generates a covering sieve of the fpqc topology.
3. Apply the source library's covering-family descent theorem to `IsFinite`, using
   the canonical pullback squares and the hypotheses on their second projections. -/
theorem isFinite_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsFinite (pullback.snd f (g i))) : IsFinite f := by
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @IsFinite)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
