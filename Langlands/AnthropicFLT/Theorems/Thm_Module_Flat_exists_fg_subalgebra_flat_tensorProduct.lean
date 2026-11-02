/-
Ported from `Theorems/Thm_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

theorem Module.Flat.exists_fg_subalgebra_flat_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [Algebra.FinitePresentation R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀) :=
  P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.solution s
