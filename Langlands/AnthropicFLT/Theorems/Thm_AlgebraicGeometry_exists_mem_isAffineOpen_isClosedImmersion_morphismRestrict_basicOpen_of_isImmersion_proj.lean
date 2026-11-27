/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified in Langlands-lib, 26 November 2026: FLT module names are prefixed by
`Langlands.AnthropicFLT`; `import Mathlib` is replaced by `import Langlands.MathlibBase`; the
FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof
`by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
    {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{0}} (ι : X ⟶ Proj 𝒜) [IsImmersion ι] (S : Finset X) :
    ∃ (d : ℕ) (F : A) (_ : F ∈ 𝒜 d), 0 < d ∧ (∀ x ∈ S, x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧
      IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧ IsClosedImmersion (ι ∣_ Proj.basicOpen 𝒜 F) :=
  P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution 𝒜 ι S
