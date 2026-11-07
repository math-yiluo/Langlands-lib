/-
Ported from `Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {H : Subgroup G} [H.Normal] [Fintype H] [IsDiscreteValuationRing (FixedPoints.subring R H)]
    (hH : ∀ τ : G,
      (⨅ z : FixedPoints.subring R H,
          IsDiscreteValuationRing.addVal R
            (((QuotientGroup.mk τ : G ⧸ H) • z - z : FixedPoints.subring R H) : R)) =
        ∑ h : H, IsDiscreteValuationRing.ramificationDepth R G (τ * (h : G)))
    (he : ∀ z : FixedPoints.subring R H,
      IsDiscreteValuationRing.addVal R (z : R) =
        (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
          IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z)
    (n : ℕ) :
    (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊ := by exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.solution R _ _ _ G _ _ _ H _ _ _ hH he n
