# `Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul`.

Proof (namespace `K72WS`). `support_subset_zeroLocus_of_forall_exists_pow_smul_eq_zero`: if every element
of a module `K` is killed by a power of each `a ∈ s`, the support of `K` lies in the zero locus of `s`.
`exists_pow_le_annihilator_of_support_subset`: for `K` finite and `J` finitely generated with support in
`V(J)`, some power `J^n` annihilates `K` (Mathlib's `Module.support` and annihilator lemmas).
`exists_pow_le_annihilator_of_forall_exists_pow_smul_eq_zero` combines the two for `J = span s`.

`solution`: apply the last lemma to the finite module `ker u` (exponent `n₁`) and to the finite module
`N ⧸ range u` (exponent `n₂`; the hypothesis `hc` says that a power of each `a ∈ S` moves every class
into the range). Then `N₀ = n₁ + n₂` works: `J^N₀ ⊆ J^n₁` kills `ker u`, and `J^N₀ ⊆ J^n₂` kills the
cokernel, so `a • y` lies in the range of `u` for `a ∈ J^N₀`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.K72WS.exists_pow_le_annihilator_of_support_subset`
- theorem `P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.K72WS.support_subset_zeroLocus_of_forall_exists_pow_smul_eq_zero`
- theorem `P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.K72WS.exists_pow_le_annihilator_of_forall_exists_pow_smul_eq_zero`
- theorem `P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
