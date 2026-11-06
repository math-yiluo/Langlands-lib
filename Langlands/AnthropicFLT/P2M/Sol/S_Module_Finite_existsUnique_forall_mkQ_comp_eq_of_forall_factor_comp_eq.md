# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq.solution` proves the
statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq`.

Proof (a single tactic proof). The ported theorems `AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply`
and `AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply` give a bijection
`θ : AdicCompletion I (Hom(M, N)) → Hom(M, AdicCompletion I N)`. The compatible maps `ψ n`, extended by `0` at level
`0` (where the quotient is trivial), define `Ψ : M → AdicCompletion I N` by `AdicCompletion.lift`. Existence: take
`x` with `θ x = Ψ` and `Φ n := x (n+1)`; the formula for `θ` gives `mkQ ∘ g = ψ n` for every representative `g` of
`Φ n`. Uniqueness: another compatible `Φ'` with the same property defines an element `x'` of the completion with
`θ x' = Ψ`, so `x' = x` by injectivity of `θ`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply` (same contribution).
Other imports: `Mathlib`.
