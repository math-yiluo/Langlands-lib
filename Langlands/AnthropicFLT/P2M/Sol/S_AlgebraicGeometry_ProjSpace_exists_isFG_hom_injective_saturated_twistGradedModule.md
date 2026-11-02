# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 18 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 21 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry`: namespace `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry` dropped.
- 1 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 42 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule`. Statement. `AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule`: for a finite morphism
`φ : X ⟶ ℙᴺ_A` with `φ ≫ ProjSpace.π A N = π`, there are a finitely generated graded module `M'` (FLT's
`ProjSpaceCech.GradedModule A N`) and an injective graded homomorphism `ψ : M' → twistGradedModule φ π`
which is saturated: for every variable `Xⱼ` and every element `x` of degree `e` of the twist module, some
`Xⱼ^k x` lies in the image of the degree-`(e + k)` part of `M'`.

Proof (namespaces `AlgebraicGeometry.ProjSpace.GMSec`, `ProjSpaceCech.GradedModule`). Chart geometry:
overlaps and intersections of pulled-back charts are basic opens of the charts, affine since `φ` is
finite (`pullbackOverlap_eq_basicOpen`, `interI`, `isAffineOpen_interI`); transition functions satisfy
the cocycle identities on smaller opens. Section `Chart`: a compatible family is determined by one
component (`twistObjOfFun`, `val_self_injective`, `val_self_surjective`). Section `Psi`: sections of
the twist over the intersection `interI` are identified with fractions over the chart ring by products
of frame units (`PsiNum`, `PsiFun`, `Psi`, bijective by `Psi_injective` and `Psi_surjective`, via
localization arguments `stepA`–`stepC`, `surj_step1`–`surj_step3b`). Sections `MonMul`, `Build`: since
`φ` is finite, each chart ring is a finite module over the corresponding chart of `ℙᴺ`; finitely many
generators (`exists_chart_generators`, `genSet`, `genFrac`) define a free graded module `Fgen` and a map
`psi0` to the twist module, whose quotient by the kernel is the finitely generated `Mgen` with injective
`psi` (`Mgen_isFG`, `psi_injective`). Sections `Sat`, `Sat2`: every element becomes, after multiplying
by a power of a variable, a combination of the generators (`Good`, closed under sums and monomial
multiples, `psi_saturated`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.proj_basicOpen_awayMk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.pullbackOverlap_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.inf_pullbackChart_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_injective_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.frameUnit_cocycle_of_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.frameUnit_mul_swap_of_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObj_eq_of_val_eq`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.frameFamily`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.frameFamily_compat`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_val_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_val_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.val_self_injective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.val_self_surjective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObjOfFun_smul`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.interI`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.interI_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.interI_anti`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.frameProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.pullbackChart_inf_interI_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.interI_eq_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.interI_le_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.basicOpen_le_interI`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.isAffineOpen_interI`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.uTop`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.D_xMul_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistXMul_pow_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistMonMul_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistMonMul_shift_apply`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Wop`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_top`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_chart`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.invProd`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.dirProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.dirProd_mul_invProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.invProd_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.dirProd_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_prod_uTop`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiNum`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_eq_of_rel`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_add_repr`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_smul_repr`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiFun`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiFun_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiFun_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiFun_smul`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Psi`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Psi_val_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Psi_mk_val_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.exists_pow_mul_eq_zero_of_restrict_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.exists_pow_mul_eq_zero_of_restrict`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.isAffineOpen_top_inf_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.stepA`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.stepB_restrict`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.stepB`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.stepC`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Psi_injective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.exists_extend_of_affine`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.basicOpen_frameProd_le_Wop`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Wop_le_basicOpen_frameProd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.surj_step1`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.surj_step2`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.isAffineOpen_topChart_inf`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Vt`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Ot`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_Vt`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_chart_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_chart_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Ot_le_Vt_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.surj_step3a`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.surj_step3b`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.invProd_single_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_frameProd_pow`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_surjective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Psi_surjective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Psi_bijective`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.ProjSpaceCech.GradedModule.evalLin`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.ProjSpaceCech.GradedModule.evalLin_monomial`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.ProjSpaceCech.GradedModule.evalLin_X_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.ProjSpaceCech.GradedModule.evalLin_mem_grade`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.ProjSpaceCech.GradedModule.evalHom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.ProjSpaceCech.GradedModule.evalHom_one`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.monMulFrac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_monMulFrac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.prod_frameUnit_pow_eq`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.fracFun`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.exists_fracFun_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.exists_chart_generators`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.genSet`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.genSet_spec`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Gens`
- anonymous instance of `Fintype (Gens φ)`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.mem_singleton_self'`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.genTarget`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.genFrac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Psi_genFrac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.PsiNum_genFrac`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.genDeg`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.genFrac_num_mem`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.GIdx`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.gen`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Fgen`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi0Lin`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi0Lin_apply`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi0`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi0_single`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.ker_psi0_stable`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Mgen`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.mem_Mgen_grade_iff`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.mkQHom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Mgen_isFG`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi_mkQ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi_injective`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.app_awayToSection_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.awayMk_eq_sum_monomial`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.fracFun_eq_sum`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.twistObj_sum_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.eq_single_of_supp`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.sum_cast_eq_of_supp`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.Good`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi0_mem_shift_grade`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.monMul_shift_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.good_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.good_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.good_smul_monMulFrac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.good_sum`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.pullbackChart_le_Wop`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.restrictFun_prod_uTop'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec.psi_saturated`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution).
Other imports: `Mathlib`.
