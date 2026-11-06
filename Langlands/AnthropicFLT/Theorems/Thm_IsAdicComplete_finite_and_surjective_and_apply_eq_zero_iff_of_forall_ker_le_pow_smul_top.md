# `Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution I M t hI ht hker L hL`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top`:
let `R` be `I`-adically complete, `M : ℕ → Type` a family of `R`-modules with linear maps
`t n : M (n+1) → M n` such that `I^(n+1) • M n = 0`, each `t n` is surjective, `ker (t n) ≤ I^(n+1) • M (n+1)`,
and `M 0` is finite. Let `L` be a submodule of `∀ n, M n` whose elements are exactly the compatible families
(`x ∈ L ↔ ∀ n, t n (x (n+1)) = x n`). Then `L` is a finite `R`-module, every `y : M n` is the `n`-th
component of some `x ∈ L`, and for `x ∈ L`, `x n = 0` if and only if `x ∈ I^(n+1) • L`.

The proof term applies the companion solution theorem
`P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
