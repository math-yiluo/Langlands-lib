# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range`.

Proof. Helpers (`X1cAlg`, `X1cMain`): finiteness of `Hom(ker p, GK)` (`finite_hom_ker`), the Artin–Rees lifting
lemma `exists_artinRees_lift`, `lam ∘ ψ = 0` when `ψ ∈ J^m Hom` and `J^m` kills `F` (`comp_eq_zero_of_mem_pow_smul`),
and telescoping for decreasing filtrations (`anti_of_forall_succ_le`, `sub_mem_of_forall_succ_sub_mem`,
`pow_smul_top_anti`).

`solution`: let `L : Hom(B^r, GK) → Hom(ker p, GK)` be restriction. `J^(k+1)` kills `F k`, and `ε k ∘ lam k = 0`.
By hypothesis, `δ − δs n − L (y n) ∈ J^(n+1) Hom(ker p, GK)` for some `y n`. The differences
`L (y (n+2+c) − y (n+1+c))` lie in `J^(n+2+c) Hom(ker p, GK)` (telescoping with `hδsc`), so Artin–Rees (constant `c`)
gives `z n ∈ J^(n+2) Hom(B^r, GK)` with the same restriction. Put `φ' n = y (1+c) + ∑_{i<n} z i` and
`ℓ' k = ℓ k + lam k ∘ φ' k`. Then `ℓ'` is compatible with the `φ k` (the added terms `z` are killed after composing
with `lam`), lifts `ψE k ∘ p` (as `ε ∘ lam = 0`), and restricts to `lam k ∘ δ` on `ker p`, since the remaining
error lies in `J^(k+1) Hom` and is killed by `lam k`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.X1cAlg.finite_hom_ker`
- theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.X1cAlg.exists_artinRees_lift`
- theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.X1cAlg.comp_eq_zero_of_mem_pow_smul`
- theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.X1cMain.anti_of_forall_succ_le`
- theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.X1cMain.sub_mem_of_forall_succ_sub_mem`
- theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.X1cMain.pow_smul_top_anti`
- theorem `P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
