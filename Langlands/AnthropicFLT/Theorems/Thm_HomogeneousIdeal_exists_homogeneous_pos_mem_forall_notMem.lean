/-
Ported from `Theorems/Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HomogeneousIdeal.exists_homogeneous_pos_mem_forall_notMem
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (I : HomogeneousIdeal 𝒜) (hirr : I ≤ HomogeneousIdeal.irrelevant 𝒜)
    (t : Finset (HomogeneousIdeal 𝒜)) (hprime : ∀ p ∈ t, p.toIdeal.IsPrime) (havoid : ∀ p ∈ t, ¬ I ≤ p) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ t, x ∉ p :=
  P2MW.S_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem.solution I hirr t hprime havoid
