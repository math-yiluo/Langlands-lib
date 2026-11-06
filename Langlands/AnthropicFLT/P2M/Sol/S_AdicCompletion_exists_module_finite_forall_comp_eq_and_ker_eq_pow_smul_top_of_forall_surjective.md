# `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective`.

Proof (namespace `W1Aux`). `isAdicComplete_map`: for `I` finitely generated, the completion `B^` is
complete for the extended ideal `I B^`. `restrictScalars_map_pow_smul` compares `(I B^)^k • N` with
`I^k • N`. In the section `killed`, a `B`-module `M` with `I^k • M = 0` becomes a `B ⧸ I^k`-module
(`modQ`) and, through the evaluation `B^ → B ⧸ I^k`, a `B^`-module (`modC`, with `modC_isScalarTower`,
`modC_smul_def`, `modQ_mk_smul`, `modC_mk_smul`, `cauchy_smul_eq`, `smul_eq_zero_of_killed`,
`isTorsionBySet_of_killed`). `killed`: under the hypotheses of the theorem, `I^(n+1) • M n = 0`
(from `ker (t n) = I^(n+1) • ⊤` and surjectivity).

`solution`: make every `M n` a `B^`-module by `modC`; the maps `t n` are `B^`-linear (`t'`), and
`M 0` is finite over `B^`. The ported theorem
`IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top`, applied over
`B^` with the ideal `I B^`, gives that the submodule `L` of compatible families is finite over `B^`, that the
projections `pr n : L → M n` are surjective, and that `x n = 0 ↔ x ∈ (I B^)^(n+1) • L`; with
`restrictScalars_map_pow_smul` this kernel is `I^(n+1) • L`. Compatibility of the projections, the
injectivity statement and the existence of `x` with prescribed compatible components hold by
definition of `L`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.isAdicComplete_map`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.restrictScalars_map_pow_smul`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.smul_eq_zero_of_killed`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.isTorsionBySet_of_killed`
- def `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.modQ`
- def `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.modC`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.modC_smul_def`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.modQ_mk_smul`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.modC_mk_smul`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.modC_isScalarTower`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.cauchy_smul_eq`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.W1Aux.killed`
- theorem `P2MW.S_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
