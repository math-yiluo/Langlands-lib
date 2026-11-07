/-
Ported from `Theorems/Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype

set_option autoImplicit false

theorem IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] [FaithfulSMul H R]
    [IsDiscreteValuationRing (FixedPoints.subring R H)]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R H))]
    [Algebra.IsSeparable
      (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (z : FixedPoints.subring R H) :
    IsDiscreteValuationRing.addVal R (z : R) =
      (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
        IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z := by exact @_root_.P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.solution R _ _ _ H _ _ _ _ _ _ _ z
