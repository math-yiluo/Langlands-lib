/-
Ported from `Theorems/Thm_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (s : R) (hs : s ≠ 0) :
    ∃ q : Ideal R, q.IsPrime ∧ s ∉ q ∧ ringKrullDim (R ⧸ q) = 1 :=
  P2MW.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.solution hR s hs
