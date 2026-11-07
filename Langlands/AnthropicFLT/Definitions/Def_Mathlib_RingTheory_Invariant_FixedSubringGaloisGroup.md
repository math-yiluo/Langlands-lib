# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

One theorem: `FixedPoints.isGaloisGroup_subring`. For a group `G` acting faithfully (`FaithfulSMul G S`) on a
commutative ring `S` by a `MulSemiringAction`, `IsGaloisGroup G (FixedPoints.subring S G) S`: the action is
faithful, commutes with the fixed subring, and the invariants of `S` are exactly the fixed subring.

The file ends with 1 `#guard_msgs in #print axioms` checks (kept from FLT), for `FixedPoints.isGaloisGroup_subring`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `FixedPoints.isGaloisGroup_subring`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
