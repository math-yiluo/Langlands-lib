/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Cardinality of the arrows of a walking multicospan

The arrows of `WalkingMulticospan J` are the identities of the objects `left a`, `right b` and
the morphisms `fst b`, `snd b`, so there are fewer than `κ` of them as soon as `J.L` and
`J.R` have fewer than `κ` elements, for an infinite cardinal `κ`.
-/

@[expose] public section

universe w w' u

namespace CategoryTheory.Limits

/-- If `J.L` and `J.R` have cardinality `< κ` for an infinite cardinal `κ`, then so does the
type of arrows of `WalkingMulticospan J`. -/
lemma hasCardinalLT_arrow_walkingMulticospan {J : MulticospanShape.{w, w'}}
    {κ : Cardinal.{u}} (hL : HasCardinalLT J.L κ) (hR : HasCardinalLT J.R κ)
    (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Arrow (WalkingMulticospan J)) κ := by
  have : HasCardinalLT (J.L ⊕ J.R ⊕ J.R ⊕ J.R) κ := by
    simpa only [hasCardinalLT_sum_iff _ _ _ hκ] using ⟨hL, hR, hR, hR⟩
  refine this.of_surjective (Sum.elim (fun a ↦ Arrow.mk (𝟙 (WalkingMulticospan.left a)))
    (Sum.elim (fun b ↦ Arrow.mk (𝟙 (WalkingMulticospan.right b)))
      (Sum.elim (fun b ↦ Arrow.mk (WalkingMulticospan.Hom.fst b))
        (fun b ↦ Arrow.mk (WalkingMulticospan.Hom.snd b))))) ?_
  rintro ⟨a, b, f⟩
  cases f with
  | id a =>
    cases a with
    | left a => exact ⟨Sum.inl a, rfl⟩
    | right b => exact ⟨Sum.inr (Sum.inl b), rfl⟩
  | fst b => exact ⟨Sum.inr (Sum.inr (Sum.inl b)), rfl⟩
  | snd b => exact ⟨Sum.inr (Sum.inr (Sum.inr b)), rfl⟩

end CategoryTheory.Limits
