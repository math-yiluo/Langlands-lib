# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt`. Statement. `AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt` (adding
one chart): let `π : V ⟶ Spec R` be separated and `M` a module with quasi-coherent FLT presheaf. If the
ordered affine cover `K'` consists of the members of `K` (embedded by an order embedding `e`
preserving the opens) plus one further member `j₀` larger than all of them, then the Čech cohomology
groups of `M` for `K'` and for `K` are isomorphic in every degree.

Proof (namespace `P2mAdjoinChart`). Section `Restrict`: restriction of an FLT presheaf to an open
subscheme (`restrictOpen`), preserving quasi-coherence. Section `Cover` and `Acyclic`: the cover `K`
restricted to the affine open `U = K'.U j₀` (`coverOn`, affine by separatedness) has vanishing higher
Čech cohomology for the restricted quasi-coherent presheaf (ported affine acyclicity,
`subsingleton_HSucc_restrictOpen`). Sections `Snoc` and `Chains`: index tuples of `K'` are either images
of tuples of `K` (`idxE`) or such tuples followed by `j₀` (`snocIdx`, `vtx`, `idx_cases`), with the
corresponding intersections (`inter_idxE`, `inter_snocIdx`). Section `Main`: the restriction map
`fMap : C(K') → C(K)` is a surjective map of complexes (`fMap_surjective`, `d_fMap`); its kernel
consists of cochains supported on tuples containing `j₀`, which form (up to shift) the Čech complex of
the cover `K` of `U`, augmented by `M(U)`; it is acyclic (`hex0` in degree `0` using the sheaf property
of `M`, `hexS_zero`, `hexS_succ` in higher degrees using acyclicity on `U`), so `fMap` induces
isomorphisms on cohomology (`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.appIso_inv_comp_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.appIso_inv_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.appIso_inv_map`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.restrictOpen`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.restrictOpen_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.restrictOpen_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.res_irrel`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.res_res_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.isQuasicoherent_restrictOpen`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.image_preimage`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.mem_iInf_fin`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.preimage_iInf`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.coverOn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.coverOn_U`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.image_inter`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.subsingleton_HSucc_restrictOpen`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.exists_d_eq_of_subsingleton_HSucc`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.snoc'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.snoc'_castSucc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.snoc'_last`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.fin_one_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.idxE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.idxE_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.idxE_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.strictMono_snoc`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.snocIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.snocIdx_apply_castSucc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.snocIdx_apply_last`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.vtx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_snocIdx_last`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_snocIdx_castSucc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_snocIdx_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_snocIdx_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.snocIdx_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.idxE_ne_snocIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.idxE_ne_vtx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.idx_cases`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.idx_cases_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.inter_idxE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.inter_snocIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.inter_vtx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.cochain_congr'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.res_dcongr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.res_zsmul_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.cochain_congr`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.fMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.fMap_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.d_fMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.fMap_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.apply_idxE_eq_zero_of_fMap_eq_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.sing`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.eq_sing`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.cov_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.le_iSup_cov`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.Msh`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.hex0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.pairIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_pairIdx_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_pairIdx_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.inf_cov_le_inter_pair`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_pair_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_pair_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.face_pair_two`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.res_pair_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.hexS_zero`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.U₀`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.KU`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.G`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.eqA`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.hexS_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.P2mAdjoinChart.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_isQuasicoherent` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` (Library), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact` (same contribution).
Other imports: `Mathlib`.
