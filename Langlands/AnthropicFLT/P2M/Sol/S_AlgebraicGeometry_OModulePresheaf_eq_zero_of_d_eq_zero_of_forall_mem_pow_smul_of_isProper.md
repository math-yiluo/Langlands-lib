# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper`.

Proof. Namespace `FormalGAGAFiniteSepAux`: combinatorics of `0`- and `1`-simplices of the cover (`vertex`,
`edge`, faces, `exists_edge`), the consequence of `d z = 0` that the components of `z` agree on every open inside
two charts (`res_eq_res_of_d_eq_zero`), points of basic opens of an affine open in terms of prime ideals
(`mem_basicOpen_iff_notMem`), and `res_basicOpen_eq_zero_of_smul_eq_zero` (if `r • m = 0` then `m` vanishes on
`D(r)`).

`solution`. (1) On each chart `K.inter s` (affine, with noetherian ring of sections and finite module `F`), the
component `z s` lies in `⋂ J^k • F` for the extended ideal `J = I Γ`, so by Krull's intersection theorem
(`Ideal.mem_iInf_smul_pow_eq_bot_iff`) there is `r s ≡ 1 mod J` with `r s • z s = 0`. (2) Let `W` be the union of
the basic opens `D(g)` of the charts on which the corresponding component of `z` vanishes. Every point `x` with
`I ⊆ q(x)` lies in `W`: on a chart containing `x`, `r s ∉ p_x` since `r s - 1 ∈ J ⊆ p_x`. (3) `W = P`: the image
under the closed map `q` of the complement of `W` is a closed set `V(J')` of `Spec A` not meeting `V(I)`, so
`J' + I = A`; as `I` lies in the Jacobson radical (`IsAdicComplete.le_jacobson_bot`), `J'` contains a unit, and
the complement is empty. (4) Hence every point of a chart has a basic-open neighbourhood on which `z s` vanishes
(using `res_eq_res_of_d_eq_zero` to pass between charts); finitely many cover the chart (quasi-compactness), and
the Library theorem `OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero` gives `z s = 0`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux`)
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux`)
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.inter_zero`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.isAffineOpen_inter_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.vertex`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.idx0_ext`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.edge`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.face_edge_zero`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.face_edge_one`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.eq_vertex`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.exists_edge`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.inter_face_inf_le`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.res_congr_idx`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.res_face_eq_of_d_eq_zero`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.res_eq_res_of_d_eq_zero`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.mem_basicOpen_iff_notMem`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.FormalGAGAFiniteSepAux.res_basicOpen_eq_zero_of_smul_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero` (Library).
Other imports: `Mathlib`.
