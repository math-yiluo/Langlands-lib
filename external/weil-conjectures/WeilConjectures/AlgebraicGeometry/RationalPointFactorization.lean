/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!

# Morphisms from spectra of fields through a rational point

Let `f : X ⟶ Spec k` and `y : Spec k ⟶ X` a `k`-point (`y ≫ f = 𝟙`). A morphism
`g : Spec K ⟶ X` from the spectrum of a field whose image is the point `y` factors through `y`:
`g = (g ≫ f) ≫ y` when `y` is a closed immersion (`AlgebraicGeometry.Scheme.eq_comp_of_apply_eq`):
the base change of `y` along `g` is a surjective closed immersion onto the reduced `Spec K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {k K : Type u} [Field k] [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (y : Spec (.of k) ⟶ X) (hy : y ≫ f = 𝟙 _)

include hy in
/-- A morphism from the spectrum of a field to `X` with image a `k`-point `y` that is a closed
immersion factors through `y`: `g = (g ≫ f) ≫ y`. -/
theorem eq_comp_of_apply_eq [IsClosedImmersion y] (g : Spec (.of K) ⟶ X)
    (hg : g.base (IsLocalRing.closedPoint K) = y.base (IsLocalRing.closedPoint k)) :
    g = (g ≫ f) ≫ y := by
  have : Surjective (pullback.snd y g) := by
    refine ⟨fun z ↦ ?_⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    have : g.base (IsLocalRing.closedPoint K) ∈ Set.range y.base := ⟨_, hg.symm⟩
    rw [← Set.mem_preimage, ← Scheme.Pullback.range_snd] at this
    exact this
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd y g)
  have h : g = inv (pullback.snd y g) ≫ pullback.fst y g ≫ y := by
    rw [pullback.condition, IsIso.inv_hom_id_assoc]
  have h' : inv (pullback.snd y g) ≫ pullback.fst y g = g ≫ f := by
    conv_rhs => rw [h]
    simp [hy]
  rw [← h', Category.assoc, ← h]

end AlgebraicGeometry.Scheme
