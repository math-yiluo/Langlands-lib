# `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`.

Proof (one term, no auxiliary declarations): the coset identity
`IsDiscreteValuationRing.iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top hA hx hy hy'`
supplies the hypothesis `hH` of
`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`, which
is applied with `he` and `n`. The file keeps FLT's line
`attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top`, `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`.
Other imports: `Mathlib`.
