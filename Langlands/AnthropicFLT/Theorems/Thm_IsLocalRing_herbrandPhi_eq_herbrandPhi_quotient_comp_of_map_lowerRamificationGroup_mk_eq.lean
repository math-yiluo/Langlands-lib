/-
Ported from `Theorems/Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-simp] IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false

theorem IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup S (G ⧸ H) ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊)
    {u : ℚ} (hu : 0 ≤ u) :
    IsLocalRing.herbrandPhi R G u =
      IsLocalRing.herbrandPhi S (G ⧸ H) (IsLocalRing.herbrandPhi R H u) := by exact @_root_.P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.solution R _ _ G _ _ _ S _ _ H _ _ hH u hu
