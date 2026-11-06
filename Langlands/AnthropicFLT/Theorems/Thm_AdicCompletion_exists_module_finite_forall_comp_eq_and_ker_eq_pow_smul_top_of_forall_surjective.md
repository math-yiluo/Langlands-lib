# `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.solution I hI M t ht hker hfin`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective`:
let `I` be a finitely generated ideal of `B`, and `t n : M (n+1) → M n` surjective `B`-linear maps with
`ker (t n) = I^(n+1) • M (n+1)` and `M 0` finite over `B`. Then there is a `B`-module `L` that is also a
finite module over the adic completion `AdicCompletion I B` (with compatible scalar actions), with `B`-linear
maps `pr n : L → M n` such that `t n ∘ pr (n+1) = pr n`, an element with all `pr n x = 0` is `0`, every
compatible family is `(pr n x)_n` for some `x`, each `pr n` is surjective and `ker (pr n) = I^(n+1) • L`.
So `L` is the inverse limit of the system, finite over the completion.

The proof term applies the companion solution theorem
`P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective` (same contribution).
Other imports: `Mathlib`.
