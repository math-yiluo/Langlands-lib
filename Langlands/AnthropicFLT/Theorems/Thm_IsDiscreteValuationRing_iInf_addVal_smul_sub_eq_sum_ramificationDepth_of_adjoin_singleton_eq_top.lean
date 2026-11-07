/-
Ported from `Theorems/Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype

set_option autoImplicit false

theorem IsDiscreteValuationRing.iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {A : Type*} [CommSemiring A] [Algebra A R]
    (hA : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {H : Subgroup G} [H.Normal] [Fintype H]
    {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    {y : R} (hy : y ∈ FixedPoints.subring R H)
    (hy' : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y}) (τ : G) :
    (⨅ z : FixedPoints.subring R H,
        IsDiscreteValuationRing.addVal R
          (((QuotientGroup.mk τ : G ⧸ H) • z - z : FixedPoints.subring R H) : R)) =
      ∑ h : H, IsDiscreteValuationRing.ramificationDepth R G (τ * (h : G)) := by exact @_root_.P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.solution R _ _ _ G _ _ _ A _ _ hA H _ _ x hx y hy hy' τ
