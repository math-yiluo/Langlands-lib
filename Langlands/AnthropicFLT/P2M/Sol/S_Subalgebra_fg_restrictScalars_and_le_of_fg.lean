/-
Ported from `P2M/Sol/S_Subalgebra_fg_restrictScalars_and_le_of_fg.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_Subalgebra_fg_restrictScalars_and_le_of_fg

set_option autoImplicit false

universe u

theorem solution
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (T : Subalgebra A₀ A) (hT : T.FG) (T' : Subalgebra ↥T A) (hT' : T'.FG) :
    (T'.restrictScalars A₀).FG ∧ (T : Set A) ⊆ (T'.restrictScalars A₀ : Set A) := by
  classical
  obtain ⟨s, rfl⟩ := hT
  obtain ⟨t, rfl⟩ := hT'
  have key : (Algebra.adjoin (↥(Algebra.adjoin A₀ (↑s : Set A))) (↑t : Set A)).restrictScalars A₀ =
      Algebra.adjoin A₀ ((↑s : Set A) ∪ ↑t) :=
    (Algebra.adjoin_union_eq_adjoin_adjoin A₀ (↑s : Set A) ↑t).symm
  refine ⟨⟨s ∪ t, ?_⟩, ?_⟩
  · rw [key, Finset.coe_union]
  · rw [key]
    exact Algebra.adjoin_mono Set.subset_union_left
