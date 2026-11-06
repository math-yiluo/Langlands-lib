# `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.solution I₀ hI₀ M₀ t₀ M t κ hκ hκt L₀ pr₀ hpr₀c hpr₀i hpr₀t hpr₀s hpr₀k L pr hprc hpri hprt hprs hprk f hf`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AdicCompletion.exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top`:
let `B` be a noetherian `B₀`-algebra, `I₀` a finitely generated ideal of `B₀`, and `B^`, `B₀^` the completions
for `I₀ B` and `I₀`. Let `t₀ n : M₀ (n+1) → M₀ n` be `B₀`-linear and `t n : M (n+1) → M n` `B`-linear, with
base-change maps `κ n : M₀ n → M n` (`IsBaseChange B (κ n)`) compatible with `t₀` and `t`. Let `L₀` be a finite
`B₀^`-module with projections `pr₀ n : L₀ → M₀ n` making it the inverse limit of `M₀` (compatible, jointly
injective, every compatible family is attained, each `pr₀ n` surjective with kernel `I₀^(n+1) • L₀`), and
`L` a finite `B^`-module with projections `pr n` making it the inverse limit of `M` in the same sense (kernels
`(I₀ B)^(n+1) • L`). Let `f : B₀^ → B^` be a ring map compatible with `B₀ → B`. Then, with `B^` a `B₀^`-algebra
through `f`, there is a bijective `B^`-linear map `e : B^ ⊗[B₀^] L₀ → L` with
`pr n (e (1 ⊗ x₀)) = κ n (pr₀ n x₀)` for all `n` and `x₀`.

The proof term applies the companion solution theorem
`P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AdicCompletion.exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
