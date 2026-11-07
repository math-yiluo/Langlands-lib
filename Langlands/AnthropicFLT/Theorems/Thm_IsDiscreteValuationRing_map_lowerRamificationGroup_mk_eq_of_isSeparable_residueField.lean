/-
Ported from `Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    {H : Subgroup G} [H.Normal] (n : ℕ) :
    (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊ := by exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.solution R _ _ _ G _ _ _ _ _ _ H _ n
