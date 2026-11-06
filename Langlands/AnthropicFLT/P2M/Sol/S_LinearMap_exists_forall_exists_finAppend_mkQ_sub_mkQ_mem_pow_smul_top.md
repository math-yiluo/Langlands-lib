# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.solution` proves the
statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top`.

Proof. Helpers (`X1aOverlapSol`): the projections `π₁`, `π₂` of `B^(r₁+r₂) = B^{r₁} × B^{r₂}` and their relation to
`Fin.append` (`π₁_append`, `π₂_append`, `append_π`).

`solution`: take `c₀` from `hlami` and `c₂` from the ported theorem
`LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul` for `Hom(ker P, GK)`; put `c = c₀ + c₂`. Lift `p₂`
along `p₁` and `p₁` along `p₂` (projectivity) to get maps `a₁ : B^(r₁+r₂) → B^{r₁}`, `a₂ : B^(r₁+r₂) → B^{r₂}` over
`GE` that are the identity on the respective summand; they restrict to `A₁ : ker P → ker p₁`, `A₂ : ker P → ker p₂`.
Set `δ₁' = δ₁ ∘ A₁`, `δ₂' = δ₂ ∘ A₂`; the first two claims hold because `a₁`, `a₂` fix the summands. For the third,
`L = ℓ₁ ∘ a₁ − ℓ₂ ∘ a₂` takes values in `ker ε = range lam`, so it lifts to `H : B^(r₁+r₂) → GK`; then
`D = δ₁' − δ₂' − H|_{ker P}` is killed by `lam (n + c)`, so its image lies in `J^(n+1+c₂) GK`, hence
`D ∈ J^(n+1) • Hom(ker P, GK)`; since `H|_{ker P}` extends to `B^(r₁+r₂)`, the classes satisfy
`[δ₁'] − [δ₂'] = [D] ∈ J^(n+1) • Ext`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.X1aOverlapSol.π₁`
- abbrev `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.X1aOverlapSol.π₂`
- theorem `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.X1aOverlapSol.π₁_append`
- theorem `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.X1aOverlapSol.π₂_append`
- theorem `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.X1aOverlapSol.append_π`
- theorem `P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul` (same contribution).
Other imports: `Mathlib`.
