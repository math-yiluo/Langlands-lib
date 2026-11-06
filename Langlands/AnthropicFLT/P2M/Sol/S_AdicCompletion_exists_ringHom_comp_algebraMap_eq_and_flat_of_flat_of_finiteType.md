# `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType`.

Proof (namespace `W7aAux`). Write `B₀^` for the `I₀`-adic completion and `Bt := B₀^ ⊗[B₀] B`, with ideals
`It := I₀ Bt` and `IB := I₀ B`. `g : B → Bt` is `b ↦ 1 ⊗ b`. `mem_pow_smul_top_of_evalₐ_eq_zero` and
`tmul_mem_pow` control `I₀`-powers; `surj`: `B → Bt ⧸ It^k` is surjective (approximate `r ⊗ b` by
`b₀ • b` with `b₀ ≡ r` mod `I₀^k`); `ker_eq`: its kernel is `IB^k`, using the map `ψ k : Bt → B ⧸ IB^k`
(`ψ_g`, `pow_le_ker_ψ`).

`solution`: `B₀^` is noetherian and `Bt` is of finite type over it, hence noetherian; `Bt` is flat over `B₀^`
(base change of the flat `B₀ → B`) and its `It`-adic completion is flat over `Bt`, so the completion
`Bt^` is flat over `B₀^` (`Module.Flat.trans`). The ported theorem
`AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow` applied to
`g` (with `surj`, `ker_eq`) gives `e : B^ ≃ Bt^` compatible with `g`. Then `f := e⁻¹ ∘ (B₀^ → Bt^)` is
compatible with the structure maps, and it is flat as a composite of a flat map and an isomorphism.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.mem_pow_smul_top_of_evalₐ_eq_zero`
- def `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.g`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.g_apply`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.g_comp_algebraMap`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.tmul_mem_pow`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.surj`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.pow_le_comap`
- def `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.ψ`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.ψ_g`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.pow_le_ker_ψ`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.W7aAux.ker_eq`
- theorem `P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow` (same contribution).
Other imports: `Mathlib`.
