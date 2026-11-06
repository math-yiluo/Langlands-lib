# `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution I hI E τ hτs hτk`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system`: let `R` be a
commutative ring with a finitely generated ideal `I`, and `E k` an inverse system of `R`-modules with surjective
transition maps `τ k` of kernel `I^(k+1) • ⊤`. Then the submodule `L` of `∏ E k` of compatible families (the
inverse limit; first conjunct characterises it) has surjective projections `L → E k`, and the kernel of the
`k`-th projection is `I^(k+1) • L`.

The proof term applies the companion solution theorem
`P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system` (same contribution).
Other imports: `Mathlib`.
