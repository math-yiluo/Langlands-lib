/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜) [IsAffineHom ι] (S : Finset X) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W :=
  P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj.solution 𝒜 ι S
