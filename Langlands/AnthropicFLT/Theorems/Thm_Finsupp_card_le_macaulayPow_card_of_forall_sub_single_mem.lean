/-
Ported from `Theorems/Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.P2M.Sol.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem
    (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card :=
  P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.solution n d hd B hB C hC hCB
