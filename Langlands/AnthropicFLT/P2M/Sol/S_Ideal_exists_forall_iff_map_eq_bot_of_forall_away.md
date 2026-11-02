# `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_iff_map_eq_bot_of_forall_away`. Statement. `Ideal.exists_forall_iff_map_eq_bot_of_forall_away`: let `P` be a property of `A`-algebras that is stable under
further maps and local for Zariski covers, and let `r_i` generate the unit ideal of `A` with ideals `K_i ⊆ A_{r_i}`
such that an `A_{r_i}`-algebra satisfies `P` iff it kills `K_i`. Then there is an ideal `I ⊆ A` such that an
`A`-algebra satisfies `P` iff it kills `I`.

Proof. Reduce to finitely many `r_i` (`finite_case`). Take `I` to be the set of `a ∈ A` whose image in each `A_{r_i}`
lies in `K_i`. An algebra satisfying `P` kills each `K_i` after localization, hence kills `I` (an element killed by a
power of every `r_i` is zero, local `eq_zero_of_forall_pow_mul_eq_zero`); conversely, if `I` is killed, then on each
localization the image of `K_i` is killed (the `K_i` agree on overlaps by uniqueness of cutting ideals, and elements
of `K_i` are multiples of images of elements of `I` up to powers of `r_i`), so `P` holds locally and hence globally.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.IdealCutAux.eq_zero_of_forall_pow_mul_eq_zero`
- theorem `P2MW.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.IdealCutAux.finite_case`
- theorem `P2MW.S_Ideal_exists_forall_iff_map_eq_bot_of_forall_away.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
