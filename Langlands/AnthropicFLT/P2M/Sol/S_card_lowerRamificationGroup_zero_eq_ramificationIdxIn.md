# `Langlands.AnthropicFLT.P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`.

Proof (two steps): rewrite `G_0` as the inertia subgroup of `maximalIdeal B`
(`IsLocalRing.lowerRamificationGroup_zero_eq_inertia`) and apply `Ideal.card_inertia_eq_ramificationIdxIn'` of
`Def_Compat_Mathlib430` (the cardinality of the inertia group under a separable residue field extension) to
`maximalIdeal A`, `hp` and `maximalIdeal B`. There are no auxiliary declarations.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_DifferentFiltrationFormula`, `Langlands.AnthropicFLT.Definitions.Def_Compat_Mathlib430`.
Other imports: `Mathlib.NumberTheory.RamificationInertia.Galois`.
