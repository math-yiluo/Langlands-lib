/-
Ported from `P2M/Sol/S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis

universe u v w u'

open CategoryTheory Opposite TopologicalSpace

theorem solution {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G : TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ := by
  haveI := TopCat.Opens.coverDense_inducedFunctor hB
  haveI : IsIso (Functor.whiskerLeft (inducedFunctor B).op φ.1) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro i
    exact h i.unop
  exact Functor.IsCoverDense.iso_of_restrict_iso φ this
