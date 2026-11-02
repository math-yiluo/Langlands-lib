# `Langlands.AnthropicFLT.P2M.Sol.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. Write `x = a / b` with `b ≠ 0`. If `b ∣ a` we are done. Otherwise the image of `a` in
`R ⧸ (b)` is nonzero, so its annihilator lies in an associated prime `p` of `R ⧸ (b)`
(`exists_le_isAssociatedPrime_of_isNoetherianRing`). By
`IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes`, `p` has height `1`; the hypothesis gives
`s ∉ p` with `s a ∈ (b)`, so `s` annihilates the image of `a` and lies in `p`, a contradiction.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes` (same contribution).
Other imports: `Mathlib`.
