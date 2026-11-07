# The order of the inertia group is the ramification index

Module `Langlands.AnthropicFLT.Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`.

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups.

## Statement

`card_lowerRamificationGroup_zero_eq_ramificationIdxIn` (root namespace): let `A` and `B` be local Dedekind domains,
`B` a finite torsion-free `A`-algebra, `G` a finite group acting on `B` with `IsGaloisGroup G A B`, such that
`maximalIdeal B` lies over `maximalIdeal A`, the residue field extension `A ⧸ 𝔪_A → B ⧸ 𝔪_B` is separable, and
`hp : maximalIdeal A ≠ ⊥`. Then `Nat.card (IsLocalRing.lowerRamificationGroup B G 0) =
(maximalIdeal A).ramificationIdxIn B`: the order of `G_0` is the ramification index.

## Proof

`exact @_root_.P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.solution A _ _ B _ _ _ _ _ G _ _ _ _ _ _ _ _ hp`: the theorem is the statement of `solution` in `Langlands.AnthropicFLT.P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean` from the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_DifferentFiltrationFormula`, `P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.solution` becomes `by exact @_root_.P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.solution` applied to the theorem's arguments in order (`_` for instance arguments).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_DifferentFiltrationFormula`, `Langlands.AnthropicFLT.P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`.
Other imports: `Mathlib.NumberTheory.RamificationInertia.Galois`.
