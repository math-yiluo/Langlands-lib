# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 16 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry`: namespace `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry` dropped.
- 30 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv`. Statement. `AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv`: for an affine morphism
`φ : X ⟶ ℙᴺ_A` and `m`, for every nonempty set `I` of indices the sections over `I` of the graded-module
Čech complex of the shifted twist module (`ProjSpaceCech.GradedModule.sec`) are isomorphic to the
sections of the twist `φ^* 𝒪(m)` over the intersection `⋂_{i ∈ I} φ⁻¹ D₊(Xᵢ)`, compatibly with the
inclusions for `I ⊆ J` and the restriction maps.

Proof (namespace `AlgebraicGeometry.ProjSpace.GMSec`; the same chart machinery as in
`ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule`). The intersections `interI` are basic
opens of the affine charts; sections of the twist over them are determined by one component
(`twistObjOfFun`, `val_self_injective`, `val_self_surjective`). The graded-module sections are fractions
`x / (∏_{i ∈ I} Xᵢ)^k` of elements of the twist module; the map `Psi` (through `PsiNum`, `PsiFun`,
using the products of frame units `dirProd`, `invProd`) sends them to sections over `interI`, is
well defined and bijective (`Psi_injective`, `Psi_surjective`, via `stepA`–`stepC` and
`surj_step1`–`surj_step3b`, localization arguments on the affine charts), and is compatible with
`secIncl` and restriction.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.proj_basicOpen_awayMk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.pullbackOverlap_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.inf_pullbackChart_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_injective_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.frameUnit_cocycle_of_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.frameUnit_mul_swap_of_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistObj_eq_of_val_eq`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.frameFamily`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.frameFamily_compat`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_val_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_val_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.val_self_injective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.val_self_surjective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_smul`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.interI`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.interI_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.interI_anti`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.frameProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.pullbackChart_inf_interI_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.interI_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.interI_le_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.basicOpen_le_interI`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.isAffineOpen_interI`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.uTop`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.D_xMul_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistXMul_pow_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistMonMul_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.twistMonMul_shift_apply`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Wop`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_top`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_chart`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.invProd`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.dirProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.dirProd_mul_invProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.invProd_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.dirProd_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_prod_uTop`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiNum`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_eq_of_rel`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_add_repr`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_smul_repr`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiFun`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiFun_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiFun_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiFun_smul`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi_val_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi_mk_val_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.exists_pow_mul_eq_zero_of_restrict_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.exists_pow_mul_eq_zero_of_restrict`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.isAffineOpen_top_inf_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.stepA`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.stepB_restrict`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.stepB`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.stepC`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi_injective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.exists_extend_of_affine`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.basicOpen_frameProd_le_Wop`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_basicOpen_frameProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.surj_step1`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.surj_step2`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.isAffineOpen_topChart_inf`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Vt`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Ot`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_Vt`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_chart_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_chart_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_Vt_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.surj_step3a`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.surj_step3b`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.invProd_single_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_frameProd_pow`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_surjective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi_surjective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi_bijective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.invProd_eq_prod_dite`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_invProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.secIncl_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi_secIncl`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.invProd_change`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.GMSec.Psi_eq_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution).
Other imports: `Mathlib`.
