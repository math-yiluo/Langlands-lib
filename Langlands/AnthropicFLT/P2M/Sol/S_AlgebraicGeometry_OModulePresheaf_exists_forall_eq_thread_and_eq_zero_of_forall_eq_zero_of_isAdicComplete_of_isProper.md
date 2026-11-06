# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_reactivate "N₁ N₂ …"` (from `P2M.Util`; it re-activates the scoped declarations of the namespaces) is replaced by `open scoped N₁ N₂ …`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper`.

Proof (namespace `K72W4`). `mem_smul_top_pi_iff` and `smul_top_mem_map` handle `I • ⊤` in finite products and
under linear maps. `core` is the abstract limit argument: given a linear map `d : C0 → C1`, additive maps
`lam0 n : C0 → L0 n` (surjective, kernel `I^(n+1) • ⊤`) and `lam1 n` (kernel inside `I^(n+1) • ⊤`)
compatible with maps `dn n : L0 n → L1 n` and transition maps `τ n`, and assuming that every sequence of
approximate cocycles converging `I`-adically has a unique cocycle limit (`H`), the map `a ↦ (lam0 n a)_n`
is injective on cocycles and every compatible family `ℓ` with `dn n (ℓ n) = 0` comes from a cocycle.

Section `Bridge`: for an ordered affine cover `K`, `E0` and `E1` identify Čech `0`- and `1`-cochains with
families over the members `K.U i` and over the pairwise intersections `pairU` (`E1_d0` computes the
differential), so that `0`-cocycles are compatible families (`d0_eq_zero_iff`, `mem_H0_iff`). Section
`Cover`: `KY` is the ordered affine cover of `Y` by the preimages under `t` of the charts of `K'` over `W`
(`iSup_preimage_chart_eq_top`).

`solution`: with `J := I R`, apply `core` to the Čech complex of `G` on `KY`, with `L0 n` the families of
sections of `F' n` on the charts and `lam0 n`, `lam1 n` given by `θ n` (surjectivity and kernels from
`hθo`, `hθk`; compatibility from `hθr`, `hθφ`). The hypothesis `H` is the ported theorem
`existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper` for the proper morphism
`sY` (with `R` complete for `J` by `hRc`). This gives the existence and injectivity statements. The
finite set `s` comes from finiteness of `H⁰(KY)` over `R` (ported `cechFinite_of_isProper`): its image
under `E0` is the submodule of compatible families, which is finitely generated.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.mem_smul_top_pi_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.smul_top_mem_map`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.core`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.σ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.σ_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.eq_σ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.le_inter_σ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.inter_le_fst`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.pairU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.inter_le_pairU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.pairU_le_inter`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.res_congr_idx`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.E0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.E0_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.E1`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.E1_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.face_zero_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.face_one_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.E1_d0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.σ₂`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.σ₂_fst`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.σ₂_snd`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.d0_eq_zero_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.mem_H0_iff`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.KY`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.KY_U`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4.iSup_preimage_chart_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library).
Other imports: `Mathlib`.
