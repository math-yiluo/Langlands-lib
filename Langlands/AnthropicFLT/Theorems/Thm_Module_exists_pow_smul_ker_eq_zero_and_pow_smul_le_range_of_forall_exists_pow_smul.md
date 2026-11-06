# `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.solution S J hJ u hker hcoker hk hc`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul`: let `S` be a
finite subset of a commutative ring `R` generating the ideal `J`, and `u : M → N` an `R`-linear map with
finitely generated kernel and finite cokernel `N ⧸ range u`. Assume that for each `a ∈ S` every element of
`ker u` is killed by some power of `a`, and every `y : N` has some `a^k • y` in the range of `u`. Then there
is `N₀` such that every `a ∈ J^N₀` kills `ker u` and maps every `y : N` into the range of `u`
(`∃ x, u x = a • y`).

The proof term applies the companion solution theorem
`P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul` (same contribution).
Other imports: `Mathlib`.
