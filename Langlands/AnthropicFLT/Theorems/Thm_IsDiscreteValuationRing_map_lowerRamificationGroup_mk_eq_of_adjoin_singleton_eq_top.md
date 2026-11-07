# Herbrand's quotient theorem in the monogenic case

Module `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`: under the hypotheses of the
monogenic coset identity (`R` a discrete valuation ring with a faithful `G`-action, `A` with fixed image (`hA`),
`H` finite normal, `Algebra.adjoin A {x} = ⊤`, `y ∈ FixedPoints.subring R H` generating the fixed subring over `A`
(`hy`, `hy'`)), with `FixedPoints.subring R H` a discrete valuation ring and the scaling `he` (as in
`Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`),
for every `n : ℕ`:
`(lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) ⌈herbrandPhi R H n⌉₊`.

The file keeps FLT's line `attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype`.

## Proof

`exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.solution R _ _ _ G _ _ _ A _ _ hA H _ _ _ x hx y hy hy' he n`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.solution` becomes `by exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`.
Other imports: `Mathlib`.
