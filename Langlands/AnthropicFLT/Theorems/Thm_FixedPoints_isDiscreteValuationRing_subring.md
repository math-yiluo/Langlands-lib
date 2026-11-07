# The fixed subring of a finite group acting on a discrete valuation ring is a discrete valuation ring

Module `Langlands.AnthropicFLT.Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`FixedPoints.isDiscreteValuationRing_subring`: for a discrete valuation ring `R` and a finite group `H` with a
`MulSemiringAction` on `R` (no faithfulness assumed), `IsDiscreteValuationRing (FixedPoints.subring R H)`.

The file keeps FLT's line `attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype`.

## Proof

`exact @_root_.P2MW.S_FixedPoints_isDiscreteValuationRing_subring.solution R _ _ _ H _ _ _`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_FixedPoints_isDiscreteValuationRing_subring.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_FixedPoints_isDiscreteValuationRing_subring.solution` becomes `by exact @_root_.P2MW.S_FixedPoints_isDiscreteValuationRing_subring.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring`.
Other imports: `Mathlib`.
