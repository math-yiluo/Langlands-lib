# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq`.

Proof (direct). The differences `θ' k − θ k` vanish on `ϑ(GK) = ker θE`, are killed by `ε k`, and are compatible
with the `φ k`. Hence they factor through `θE` as `dbar k : GE → F k`, with values in `ker ε k = range lam k` and
compatible with `φ`. Through `GK / ker (lam k) ≅ range (lam k)` this gives a compatible family
`f k : GE → GK / ker (lam k)`. The submodules `ker (lam k)` decrease, contain `I^(k+1) GK` (as `I^(k+1)` kills `F k`)
and satisfy `ker (lam (k+c)) ⊆ I^(k+1) GK`, so the ported theorem
`LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible` gives `g k : GE → GK` with
`g (k+1) − g k ∈ I^(k+1) • Hom(GE, GK)` and `g k ≡ f k`; then `lam k ∘ g k = dbar k` and so
`θ' k − θ k = lam k ∘ g k ∘ θE`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible` (same contribution).
Other imports: `Mathlib`.
