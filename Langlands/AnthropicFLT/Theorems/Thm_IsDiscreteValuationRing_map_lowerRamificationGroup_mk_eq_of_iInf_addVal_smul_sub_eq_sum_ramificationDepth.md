# Herbrand's quotient theorem from the coset identity and the valuation scaling

Module `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`: let
`R` be a discrete valuation ring with a faithful action of a group `G`, `H` a finite normal subgroup with
`FixedPoints.subring R H` a discrete valuation ring, and assume
`hH : ∀ τ, ⨅ z : FixedPoints.subring R H, addVal R ((τH) • z - z) = ∑ h : H, ramificationDepth R G (τ * h)` and
`he : ∀ z : FixedPoints.subring R H, addVal R z = lowerRamificationCard R H 0 * addVal (FixedPoints.subring R H) z`.
Then for every `n : ℕ`,
`(lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) ⌈herbrandPhi R H n⌉₊`
(lower groups of `G ⧸ H` for its action on the fixed subring): Herbrand's theorem `G_n H/H = (G/H)_{φ_H(n)}` at
integer `n` (Serre, Local Fields, IV §3, Lemma 5 and the following theorem; for `n` integral the lower group with
real index `φ_H(n)` is the one with index `⌈φ_H(n)⌉`).

## Proof

`exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.solution R _ _ _ G _ _ _ H _ _ _ hH he n`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.solution` becomes `by exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`.
Other imports: `Mathlib`.
