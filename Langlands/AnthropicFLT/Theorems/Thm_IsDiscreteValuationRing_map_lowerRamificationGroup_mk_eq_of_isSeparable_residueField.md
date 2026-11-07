# Herbrand's quotient theorem for lower ramification groups

Module `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`: let `R` be a discrete
valuation ring and `G` a finite group acting faithfully on `R` by a `MulSemiringAction`, such that `maximalIdeal R`
lies over the maximal ideal of the fixed subring `FixedPoints.subring R G` and the residue field extension
`FixedPoints.subring R G ⧸ 𝔪 → R ⧸ 𝔪` is separable. Then for every normal subgroup `H` of `G` and every `n : ℕ`,
`(lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) ⌈herbrandPhi R H n⌉₊`,
where `G ⧸ H` acts on the fixed subring `FixedPoints.subring R H` (a local ring by
`FixedPoints.isLocalRing_subring`). For `R` the ring of integers of a finite Galois extension `L/K` of local fields
with Galois group `G` and `H = Gal(L/K')`, this is Herbrand's theorem `G_n H/H = (G/H)_{φ_{L/K'}(n)}` (Serre, Local
Fields, IV §3) at integer indices `n`; the separability hypothesis holds for finite residue fields.

## Proof

`exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.solution R _ _ _ G _ _ _ _ _ _ H _ n`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`, `P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.solution` becomes `by exact @_root_.P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`, `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`.
Other imports: `Mathlib`.
