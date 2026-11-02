/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
    {σ : Type*} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H) :
    (∀ i, IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) ∧
    (∀ i j, i ≠ j → Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange)) ∧
    (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ ∧
    (∀ i, ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u) ∧
    (CompactSpace T → {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T).Nonempty}.Finite) :=
  P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.solution H u
