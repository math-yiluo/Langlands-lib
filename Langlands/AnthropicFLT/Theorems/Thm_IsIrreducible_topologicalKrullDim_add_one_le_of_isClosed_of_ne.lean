/-
Ported from `Theorems/Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z :=
  P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.solution hZ hY hYZ hne
