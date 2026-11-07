# A finite extension of discrete valuation rings with separable residue extension is monogenic

Module `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`IsDiscreteValuationRing.exists_adjoin_singleton_eq_top_of_isSeparable_residueField`: for discrete valuation rings
`A` and `B` with an `A`-algebra structure on `B` such that `algebraMap A B` is a local homomorphism and injective
(`hinj`), `B` is a finite `A`-module and the residue field extension `ResidueField A → ResidueField B` is separable,
there is `x : B` with `Algebra.adjoin A {x} = ⊤` (Serre, Local Fields, III §6, Proposition 12).

The file keeps FLT's lines `attribute [-instance] ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal` and an `attribute [-simp]` line for five lemmas of `Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup`.

## Proof

`exact @_root_.P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.solution A _ _ _ B _ _ _ _ _ _ _ hinj`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.solution` becomes `by exact @_root_.P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField`.
Other imports: `Mathlib`.
