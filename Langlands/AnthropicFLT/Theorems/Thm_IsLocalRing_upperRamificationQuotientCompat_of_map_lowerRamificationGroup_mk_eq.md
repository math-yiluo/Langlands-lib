# Herbrand's theorem for upper ramification groups from the lower-numbering compatibility

Module `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`: under the hypotheses of
`Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq` (local rings `R`,
`S`, finite `G` acting on `R`, `H` normal, `G ⧸ H` acting on `S`, and `hH`),
`IsLocalRing.UpperRamificationQuotientCompat R G S H` holds: for every rational `v ≥ 0`,
`(upperRamificationGroup R G v).map (QuotientGroup.mk' H) = upperRamificationGroup S (G ⧸ H) v`
(`G^v H/H = (G/H)^v`, Serre, Local Fields, IV §3, Proposition 14).

The file keeps FLT's `attribute [-simp]` line for four lemmas of `Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup`.

## Proof

`exact @_root_.P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.solution R _ _ G _ _ _ S _ _ H _ _ hH`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `P2M.Sol.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.solution` becomes `by exact @_root_.P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`.
Other imports: `Mathlib`.
