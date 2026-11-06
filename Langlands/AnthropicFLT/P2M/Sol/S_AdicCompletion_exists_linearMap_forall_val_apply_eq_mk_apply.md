# `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply.solution` proves the statement
of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply`.

Proof (a single tactic proof). Composition with the quotient map `N → N / I^n N` kills `I^n • Hom(M, N)`, so it
induces `α n : Hom(M, N) / I^n Hom(M, N) → Hom(M, N / I^n N)` with `α n [g] m = [g m]`. For `x` in the completion
of `Hom(M, N)`, the maps `α n (x n)` are compatible with the transition maps (`hcompat`), so
`AdicCompletion.lift` gives `θ x : M → AdicCompletion I N`; `θ` is additive and `A`-linear by
extensionality, and the stated formula holds by `hα`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
