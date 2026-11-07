# Ramification depth on the fixed subring as a sum over a coset (monogenic case)

Module `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`IsDiscreteValuationRing.iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top`: let `R` be a
discrete valuation ring with a faithful action of a group `G`, `A` a commutative semiring with an `A`-algebra
structure on `R` whose image is fixed by every element of `G` (`hA`), `H` a finite normal subgroup of `G`, `x : R`
with `Algebra.adjoin A {x} = ⊤`, and `y ∈ FixedPoints.subring R H` such that every element of the fixed subring
lies in `Algebra.adjoin A {y}` (`hy'`). Then for every `τ : G`,
`⨅ z : FixedPoints.subring R H, addVal R ((τH) • z - z) = ∑ h : H, ramificationDepth R G (τ * h)`.
The left side is the ramification depth of `τH ∈ G ⧸ H` on the fixed subring, measured with the valuation of `R`
(Serre, Local Fields, IV §1, Proposition 3, before dividing by the ramification index).

The file keeps FLT's line `attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype`.

## Proof

`exact @_root_.P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.solution R _ _ _ G _ _ _ A _ _ hA H _ _ x hx y hy hy' τ`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `P2M.Sol.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.solution` becomes `by exact @_root_.P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top`.
Other imports: `Mathlib`.
