/-
Ported from `Theorems/Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
    {R S E K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field E] [Field K] [Algebra E K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap E K).range) :
    FiniteDimensional E (IntermediateField.adjoin E (Set.range χ')) :=
  P2MW.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range.solution χ' h
