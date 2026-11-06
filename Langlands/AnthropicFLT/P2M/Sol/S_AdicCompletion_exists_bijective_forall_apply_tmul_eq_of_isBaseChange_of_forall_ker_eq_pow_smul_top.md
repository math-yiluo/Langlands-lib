# `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Compatibility edit for the project's Mathlib: in the proof of `solution`, the case `| zero => exact ⟨0, Submodule.zero_mem _, LinearMap.map_zero _⟩` of `induction m using (hκ 0).inductionOn` is deleted. In this Mathlib, `IsBaseChange.inductionOn` has only the cases `tmul`, `smul` and `add`, so Lean rejects the `zero` case. The other cases are unchanged.

## Content

The theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `W7bAux`). Section `generic`, for a finitely generated ideal `J` of `C`: an element `r` of
the completion with `evalₐ k r = c mod J^k` differs from `c` by an element of `J^k • ⊤` and of `(J C^)^k`
(`mem_pow_smul_top_of_evalₐ_eq_zero`, `sub_of_mem_pow_smul_top`, `sub_of_mem_map_pow`); hence, for a map
`p : L → P` with kernel `J^(n+1) • L`, `p (r • x) = c • p x` (`apply_smul_eq`; also `of_eq_algebraMap`,
`of_smul`, `smul_mem_pow_smul_top`). Section `flev`: `f` maps `of b` to `of (algebraMap b)` and is
compatible with the evaluations (`map_of_eq`, `evalₐ_map_eq`).

`solution`: `L` is a module over `B₀^` through `f`. Every `x₀ : L₀` gives the compatible family
`κ n (pr₀ n x₀)`, which is `pr n` of a unique `Λ x₀ : L` (`hprt`, `hpri`); `Λ` is `B₀^`-linear by
`apply_smul_eq` and `evalₐ_map_eq`. Put `e := Λ.liftBaseChange`, so `pr n (e (1 ⊗ x₀)) = κ n (pr₀ n x₀)`.
Injectivity: the tensor product `B^ ⊗ L₀` is a finite module over the noetherian complete ring `B^`, hence
complete and Hausdorff (ported `IsAdicComplete.of_module_finite`, `isAdicComplete_map_algebraMap_of_fg`);
if `pr n (e y) = 0` then `y ∈ (I B^)^(n+1) • ⊤` — the map `μ : M n → (B^ ⊗ L₀) ⧸ (I B^)^(n+1) • ⊤`, built by
the universal property of the base change `κ n` from the map induced by `pr₀ n`, satisfies
`μ (pr n (e y)) = y mod (I B^)^(n+1)` — so `e y = e z` forces `y - z` into every power and `y = z`.
Surjectivity: the range of `e` maps onto `M 0` (induction over the base change `κ 0`), so
`L = range e + (I B^) • L` (from `hprk 0`), and Nakayama (`Submodule.le_of_le_smul_of_le_jacobson_bot`, with
`I B^` in the Jacobson radical of the complete ring) gives `range e = L`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.mem_pow_smul_top_of_evalₐ_eq_zero`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.sub_of_mem_pow_smul_top`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.sub_of_mem_map_pow`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.of_eq_algebraMap`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.of_smul`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.smul_mem_pow_smul_top`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.apply_smul_eq`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.map_of_eq`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.W7bAux.evalₐ_map_eq`
- theorem `P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isAdicComplete_map_algebraMap_of_fg` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_module_finite` (same contribution).
Other imports: `Mathlib`.
