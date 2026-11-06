# `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `P2mAdicKerAR`), an Artin–Rees argument over the adic completion. Section `Filtration`, for a
finite module `E` over a noetherian ring `B` and a decreasing family of submodules `Msub k` with
`Msub k ≤ Msub (k+1) ⊔ J^(k+1) • ⊤` (`hstep`): `Mhat` is the submodule of the completion `AdicCompletion J E`
of elements whose level-`(j+1)` component lies in the image of `Msub j`. An element `x ∈ Msub n` is refined
step by step into elements of `Msub (n+i)` congruent modulo `J^(n+i+1)` (`tseq`), giving a Cauchy sequence
and an element `xhat` of `Mhat` whose level-`(n+1)` component is the class of `x` (`eval_succ_xhat`) and
which lies in the kernel of evaluation at level `n` if `x ∈ J^n • ⊤` (`eval_xhat_eq_zero`). `core`: the
completion of `B` is noetherian and the completion of `E` is a finite module over it, so Mathlib's
Artin–Rees lemma `Ideal.exists_pow_inf_eq_pow_smul` for the extended ideal and `Mhat` gives `c`; with
`AdicCompletion.pow_smul_top_eq_ker_eval` this yields
`J^n • ⊤ ⊓ Msub n ≤ J^k • Msub n ⊔ J^(n+1) • ⊤` for `k + c ≤ n`.

Section `System`: a surjection `u0 : B^m → G 0` lifts along the surjective `γ` to compatible maps
`lifts u0 k : B^m → G k` (projectivity of `B^m`), which are surjective by a Nakayama-type argument
(`eq_top_of_sup_smul_top`, `lifts_surjective`); `J^(k+1)` kills `G k` (`pow_succ_smul_top_eq_bot`).
Section `Kernel`: the pullbacks `Msub k := (ker θ k).comap (u k)` are decreasing (`comap_ker_succ_le`) and
satisfy `hstep` (`comap_ker_le_succ_sup`, using `hφk`). `main` applies `core` to them and pushes the inclusion
forward along the surjection `u n` (`map_inf_map_le`), the term `J^(n+1) • ⊤` vanishing in `G n`.
`solution` is `P2mAdicKerAR.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.Mhat`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.mem_Mhat_iff`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.exists_mem_succ_sub_mem`
- def `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.tseq`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.tseq_zero`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.tseq_sub_succ_mem`
- def `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.cseq`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.cseq_apply`
- def `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.xhat`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.xhat_val`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.Msub_le_of_le`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.xhat_mem_Mhat`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.eval_xhat_eq_zero`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.eval_succ_xhat`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.map_eval_smul_Mhat_le`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.core`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.pow_succ_smul_top_eq_bot`
- def `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.lifts`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.comp_lifts_succ`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.lifts_zero`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.eq_top_of_sup_smul_top`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.lifts_surjective`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.comap_ker_succ_le`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.comap_ker_le_succ_sup`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.map_inf_map_le`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerAR.main`
- theorem `P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing` (Library).
Other imports: `Mathlib`.
