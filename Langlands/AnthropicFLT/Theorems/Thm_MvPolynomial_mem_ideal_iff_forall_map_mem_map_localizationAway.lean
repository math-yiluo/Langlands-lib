/-
Ported from `Theorems/Thm_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open MvPolynomial

theorem MvPolynomial.mem_ideal_iff_forall_map_mem_map_localizationAway
    {σ : Type} (A : Type uz) [CommRing A] {ι : Type*} (r : ι → A) (hr : Ideal.span (Set.range r) = ⊤)
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A) :
    f ∈ I ↔ ∀ i : ι,
      MvPolynomial.map (algebraMap A (Localization.Away (r i))) f ∈
        Ideal.map (MvPolynomial.map (algebraMap A (Localization.Away (r i)))) I :=
  P2MW.S_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway.solution A r hr I f
