/-
Ported from `Theorems/Thm_Ideal_height_map_quotientMk_span_singleton_add_one.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_height_map_quotientMk_span_singleton_add_one
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Ideal.height_map_quotientMk_span_singleton_add_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] {x : R} (hx : x ∈ p)
    (hxmin : ∀ q ∈ minimalPrimes R, q ≤ p → x ∉ q) :
    (p.map (Ideal.Quotient.mk (Ideal.span {x}))).height + 1 = p.height :=
  P2MW.S_Ideal_height_map_quotientMk_span_singleton_add_one.solution p hx hxmin
