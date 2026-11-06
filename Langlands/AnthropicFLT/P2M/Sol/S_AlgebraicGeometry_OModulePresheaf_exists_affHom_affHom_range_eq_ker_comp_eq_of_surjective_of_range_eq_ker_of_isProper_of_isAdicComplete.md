# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`.

Proof (namespace `RedC6bSol` for helpers). For a quasi-coherent `F`, restriction from an affine `U` (or from an open
`O`) to basic opens is a localization (`FO`, `instACG_FO`, `instMod_FO`, `FO_smul_def`, `FresO`, `FresO_apply`,
`Fres₀`, `Fres₀_apply`, `isLocalizedModule_FresO`, `isLocalizedModule_Fres₀`), so sections are separated and glue on
finite basic covers (`eq_of_forall_isLocalizedModule_eq`, `F_eq_of_forall_res_basicOpen_eq`,
`F_exists_of_forall_res_eq`). An affine homomorphism is `Γ(U)`-linear on affines (`appO`, `appO_apply`), induces the
localized maps on basic opens (`bU`, `appB`, `appB_comp`, `map_eq_appB`) and is determined by its values on a
basic cover (`app_eq_of_forall_basicOpen`); every affine has a finite basic cover by members of a basis (`exists_cover`).

`solution`: the ported theorem
`exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete` gives basis
data `M W` with `ϑ`, `θE`, `θF`; the ported theorem `exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`
extends `M` to a coherent quasi-coherent `G` (`e W : G(W) ≅ M W`) and induces `α : GK → G` (from `ϑ`),
`β : G → GE` (from `θE`) and `ψ k : G → F k` (from `θF k`). On an affine `U`, exactness of
`GK(U) → G(U) → GE(U)` and surjectivity of `β` are checked after localizing at a basic cover by members of the
basis, where they are the exactness of the basis data (Mathlib's `exact_of_isLocalized_span` and
`surjective_of_isLocalized_span`); the compatibilities of `ψ` with `φ`, `lam`, `ε`, `ψE` hold on members and hence everywhere by
`app_eq_of_forall_basicOpen`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.eq_of_forall_isLocalizedModule_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.FO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.instACG_FO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.instMod_FO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.FO_smul_def`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.FresO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.FresO_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.Fres₀`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.Fres₀_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.isLocalizedModule_FresO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.isLocalizedModule_Fres₀`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.F_eq_of_forall_res_basicOpen_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.F_exists_of_forall_res_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.appO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.appO_apply`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.bU`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.appB`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.appB_comp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.map_eq_appB`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.app_eq_of_forall_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol.exists_cover`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top` (same contribution).
Other imports: `Mathlib`.
