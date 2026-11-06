# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq`.

Proof (namespace `InternalHomCohSol`). Section `Algebra`: if `h i` generate the unit ideal, so do their powers
(`span_range_pow_eq_top`), an element killed by a power of every `h i` is `0`, and compatible elements of the
localisations at the `h i` glue up to a common power (`exists_pow_smul_eq_of_isLocalizedModule`,
`exists_forall_eq_of_compatible`). Section `Datum`: basic-open bookkeeping on an affine `U`; `F(D(f))` as a
`Γ(V, U)`-module (`modBO`) with the restriction `resBO`, which is the localisation at the powers of `f` when `F` is
quasi-coherent (`isLocalizedModule_resBO`, `qcAt_of_isLocalizedModule`); and `eq_zero_of_forall_res_eq_zero` (a
section of a quasi-coherent presheaf on an affine `W` that vanishes on basic opens generating the unit ideal is
`0`).

Existence and uniqueness of the extension (sections `Phi`, `Inj`, `Exist`): for a `Γ(V, U)`-linear
`f₀ : F(U) → G(U)`, `Phi g` is its localisation `F(D(g)) → G(D(g))` (`IsLocalizedModule.map`), compatible with
restriction and scalars (`Phi_res`, `Phi_smul`, `res_Phi`). A section of `internalHom F G` over `U` vanishing on
`U` itself vanishes on every basic open, hence on every affine `W ≤ U` (`apply_basicOpen_eq_zero`,
`eq_zero_of_eval_eq_zero`). For existence, `IsGlued W x z` says that `z ∈ G(W)` restricts on each basic open
`D(g) ≤ W` (`g ∈ Γ(V, U)`) to `Phi g` of the restriction of `x`; glued values are unique, additive, linear and
compatible with restriction, and exist (`exists_isGlued`, by `exists_forall_eq_of_compatible` on a cover of `W`
by basic opens of `U`). `glueFamily` collects them into a section with value `f₀` on `U`
(`existsUnique_eval_eq`).

Coherence and quasi-coherence (section `CohQcoh`): on an affine `U`, evaluation at `U` is a bijection
`evalU : internalHom F G (U) ≃ Hom_{Γ(V,U)}(F(U), G(U))` (`evalU_bijective`); the Hom module between finite
modules over the noetherian ring `Γ(V, U)` is noetherian, hence finite (`isNoetherian_linearMap`,
`isCoherent_internalHom`). On `D(f)` the analogous bijection `evalD` is compatible with restriction, and since
`F(U)` is finitely presented, Hom commutes with localisation; this gives the localisation property of the
restriction `internalHom F G (U) → internalHom F G (D(f))` (`isLocalizedModule_res_internalHom`) and hence
quasi-coherence (`isQuasicoherent_internalHom`). `main` combines the three facts and `solution` is
`InternalHomCohSol.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.span_range_pow_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.eq_zero_of_forall_pow_smul_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.exists_pow_smul_eq_of_isLocalizedModule`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.exists_forall_eq_of_compatible`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.bo_mul_le_left`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.bo_mul_le_right`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.basicOpen_res_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.algebraMap_res_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.algebraMap_basicOpen_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isUnit_algebraMap_of_le`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.modBO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.modBO_smul_def`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isScalarTower_modBO`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.resBO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.resBO_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isLocalizedModule_resBO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.qcAt_of_isLocalizedModule`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.resL`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.resL_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.map_units_of_le`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.BelowIdx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.span_res_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.eq_zero_of_forall_res_eq_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.Phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.Phi_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.Phi_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.res_Phi`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.boBelow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.apply_basicOpen_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.eq_zero_of_eval_eq_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.IsGlued`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isGlued_unique`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isGlued_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isGlued_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isGlued_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isGlued_eval`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.exists_isGlued`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.glueFun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isGlued_glueFun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.glueFun_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.glueLin`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.glueLin_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.glueFamily`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.glueFamily_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.existsUnique_eval_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.sections_map_refl_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isNoetherian_linearMap`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalU_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalU_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalU_bijective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isCoherent_internalHom`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.Daff`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalD`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalD_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalD_bijective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.evalD_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isLocalizedModule_res_internalHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.isQuasicoherent_internalHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.InternalHomCohSol.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution).
Other imports: `Mathlib`.
