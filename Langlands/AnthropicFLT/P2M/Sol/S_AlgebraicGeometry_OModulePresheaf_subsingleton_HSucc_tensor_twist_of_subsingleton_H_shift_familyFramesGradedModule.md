# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule`.

Proof (namespace `P2mGrRetract`): the Čech complex of `G k ⊗ O(d)` on the standard cover `𝔘 = stdCoverPullback ι`
is a retract of the graded Čech complex of the shifted module `Md ι hθ d = familyFramesGradedModule(d)`, so
vanishing of `H^(i+1)` of the latter forces vanishing of `HSucc i` of the former.

- Geometry and simplices (as in the neighbouring ports; `proj_basicOpen_awayToSection_ratio`, `basicOpen_frameUnit`,
  `basicOpen_prod_frameUnit`, `basicOpen_prod_frameUnit_univ`): an `i`-simplex `s` of `𝔘` is an injective chart
  choice `c s` (`c_injective`) with first chart `ch s`, identified with the Library index `ProjSpaceCech.Idx r i`
  (`toIdx`, `ofIdx`, compatible with faces); `I s` is its image (`mem_I_iff`, `c_mem_I`, `ch_mem_I`, `card_I`), and
  `W s` the intersection of its charts (`inter_eq`, `W_le*`, `W_face_le`). On `W s` the frame units `uW s l` of chart
  `ch s` are invertible for `l ∈ I s` (`isUnit_uW`, `uW_self`); `uprod`/`uPow` are monomials in them (`uprod_add`,
  `uprod_zero`, `uPow_eq`, `uPow_add`, `isUnit_uPow`), and `aN s n` the exponent `n` on `I s` (`aN_supp`, `sum_aN`,
  `uprod_aN`).
- Family: degrees `degZ`/`degN` of a fraction with exponent `a` in the shifted module (`degZ_eq`, `degZ_nonneg`,
  `toNat_degZ`, `sum_cast_add`, `degN_add`); numerators of fractions are compatible families
  (`isHomogeneousElem_num`, `framesCompat_num`); monomial multiplication on singles (`monMul_apply_top`, `rel_apply`,
  `single_add'`, `single_congr`, `monMul_single`, `uprod_cocycle`, `framesCompat_uprod_smul`, `single_mem_grade`);
  `mkSec` builds a localized section from a compatible family (`sec_mk_congr_num`, `mkSec_add`).
- `β s` (via `βraw`): a fraction `f / X^a` of the localization at `I s` goes to `uPow(a)⁻¹ · f_{ch s}|_{W s}` in
  `G k(W s)` (`uPow_smul_βraw`, `βraw_wellDefined`, `uPow_smul_βraw_mk`, `βraw_add`, `β_mk`, `uPow_smul_β_mk`); it
  intertwines the localization maps of faces with `uW^d ·` restriction (`c_face`, `I_face_subset`, `ch_face_mem`,
  `uW_face`, `uPow_face`, `res_num_face`, `β_face`).
- `α s`: by quasi-coherence of `G k`, a section `t` over `W s` has a representative compatible family `g` with
  exponent `aN s n` (`Rep`, `Rep.add`, `exists_rep`), unique up to the localization relation (`exists_torsion`,
  `rep_unique`); `α s t = mkSec` of it (`αfun`, `αfun_eq`, `αfun_add`, `α_apply`), with `β ∘ α = id`
  (`res_UW_of_rep`, `β_α`) and compatibility with faces (`Rep.face`, `α_face`).
- Untwist: on an open inside chart `j` the twist `O(d)` is trivialized by `evT` (`restrictFun_evT`, `evT_res`,
  `evT_change`: changing chart multiplies by `u_{jj'}^d`; `restrictFun_injective_of_ge`), giving
  `E : F ⊗ O(d) ≅ F` there (`E_tmul`, `E_res`).
- Chain: `AE = α ∘ E` and `BE = E⁻¹ ∘ β` on each simplex (`GT` is `G k ⊗ O(d)`; `BE_AE`, `AE_add`, `AE_zsmul`,
  `BE_add`, `BE_zsmul`, `AE_face`, `BE_face`, `neg_one_pow_smul`) assemble into cochain maps `Aco`, `Bco` with
  `Bco ∘ Aco = id` (`Bco_Aco`, `Aco_zero`, `AEh`, `BEh`) commuting with the differentials (`d_Aco`, `d_Bco`).
  `main`: a cocycle `x` maps to a cocycle `Aco x`, which is a coboundary `d b` by hypothesis, so
  `x = Bco (Aco x) = d (Bco b)`. `solution` is `P2mGrRetract.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.proj_basicOpen_awayToSection_ratio`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.basicOpen_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.basicOpen_prod_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.basicOpen_prod_frameUnit_univ`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.𝔘`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.c`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.c_injective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.ch`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.toIdx`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.ofIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.toIdx_ofIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.ofIdx_toIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.toIdx_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.ofIdx_face`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.I`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.mem_I_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.c_mem_I`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.ch_mem_I`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.card_I`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.W`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.inter_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.W_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.W_le_ch`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.W_le_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.W_le_overlap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.W_face_le`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uW`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.isUnit_uW`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uW_self`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uprod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uprod_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uprod_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uPow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uPow_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uPow_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.isUnit_uPow`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.aN`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.aN_supp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.sum_aN`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uprod_aN`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Md`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.res_smul'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.res_res_eq_self`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.degZ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.degN`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.degZ_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.degZ_nonneg`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.toNat_degZ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.sum_cast_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.degN_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.isHomogeneousElem_num`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.framesCompat_num`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.monMul_apply_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.rel_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.single_add'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.single_congr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.monMul_single`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uprod_cocycle`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.framesCompat_uprod_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.single_mem_grade`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.mkSec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.sec_mk_congr_num`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.mkSec_add`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.βraw`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uPow_smul_βraw`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.βraw_wellDefined`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uPow_smul_βraw_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.βraw_add`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.β`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.β_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uPow_smul_β_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.c_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.I_face_subset`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.ch_face_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uW_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.uPow_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.res_num_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.β_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.UW_le_U`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.UW_le_W`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Rep.add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.exists_rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.exists_torsion`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.rep_unique`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.αfun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.αfun_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.αfun_add`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.α`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.α_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.res_UW_of_rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.β_α`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Rep.face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.α_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.restrictFun_injective_of_ge`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.evT`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.restrictFun_evT`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.evT_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.evT_change`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.E`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.E_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.E_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.neg_one_pow_smul`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.GT`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.AE`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.BE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.BE_AE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.AE_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.AE_zsmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.BE_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.BE_zsmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.AE_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.BE_face`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Aco`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Bco`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Bco_Aco`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.Aco_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.AEh`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.BEh`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.d_Aco`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.d_Bco`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.P2mGrRetract.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart` (Library).
Other imports: `Mathlib`.
