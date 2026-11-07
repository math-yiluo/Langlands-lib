/-
Ported from `P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
import Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {A : Type*} [CommSemiring A] [Algebra A R]
    (hA : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {H : Subgroup G} [H.Normal] [Fintype H] [IsDiscreteValuationRing (FixedPoints.subring R H)]
    {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    {y : R} (hy : y ∈ FixedPoints.subring R H)
    (hy' : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y})
    (he : ∀ z : FixedPoints.subring R H,
      IsDiscreteValuationRing.addVal R (z : R) =
        (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
          IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z)
    (n : ℕ) :
    (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊ :=
  IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
    (IsDiscreteValuationRing.iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
      hA hx hy hy')
    he n
