/-
Ported from `Theorems/Thm_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing
theorem IsLocalRing.ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
  P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.solution hx hxmin
