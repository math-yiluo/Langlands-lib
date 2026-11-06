# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent`.

Proof (namespace `P2mQcExtFrames`): extension of a section over the intersection `W = ⋂_v ι⁻¹ D₊(X_{c v})` of charts
to a twisted compatible family, by clearing denominators. Geometry: the basic open of the frame unit `u_{ji}` in
chart `j` is the overlap, and of a product `∏_v u_{j, c v}` it is chart `j` intersected with `W`
(`proj_basicOpen_awayToSection_ratio`, `basicOpen_frameUnit`, `basicOpen_prod_frameUnit`,
`basicOpen_prod_frameUnit_univ`). Setup: `W`, `fU j = ∏_v u_{j, c v}`, the opens `OW j l` with their inclusions
(`UW_le_U`, `UW_le_W`, `OW_le_*`), and the cocycle identities `u_{jl}^(i+1) · fU l = fU j` and
`u_{jl} u_{lk} = u_{jk}` on overlaps (`frameUnit_pow_mul_prod`, `frameUnit_pow_mul_prod_res`, `frameUnit_mul_res`).
Sections (`res_smul'`, `res_res_eq_self`; charts and overlaps affine since `ι` is affine, `Uaff`, `Oaff`): by
quasi-coherence, `fU j^n · x` extends from `chart j ∩ W` to chart `j` for some `n` (`exists_numer`), and a section on
an overlap vanishing on `OW` is killed by a power of `fU j` (`exists_torsion`). Extend: put
`τ j = u_{j, c 0}^d · t|_{chart j ∩ W}`; choose a uniform `n` and lifts `y j` of `fU j^n τ j`
(`exists_numer_uniform`, `res_pow_smul`); the twisted discrepancies of the `y` on overlaps vanish on `OW`
(`discrepancy_vanishes`), so a further power `e` kills them (`ExtData`, `exists_extData`). Then
`t' j = fU j^e · y j` (`ExtData.t'`, `ExtData.key`) is compatible in degree `d + (n + e)(i + 1)`
(`ExtData.framesCompat`) and restricts to `fU j^(n+e) u_{j, c 0}^d · t` (`ExtData.res_t'`). `solution` takes
`N = n + e`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.proj_basicOpen_awayToSection_ratio`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.basicOpen_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.basicOpen_prod_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.basicOpen_prod_frameUnit_univ`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.W`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.fU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.UW_le_U`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.UW_le_W`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.OW`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.OW_le_O`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.OW_le_UWj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.OW_le_UWl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.OW_le_Uj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.OW_le_Ul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.OW_le_W'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.frameUnit_pow_mul_prod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.frameUnit_pow_mul_prod_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.frameUnit_mul_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.res_smul'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.res_res_eq_self`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.Uaff`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.Oaff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.exists_numer`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.exists_torsion`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.τ`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.ExtData`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.res_pow_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.exists_numer_uniform`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.discrepancy_vanishes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.exists_extData`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.ExtData.t'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.ExtData.key`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.ExtData.framesCompat`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.P2mQcExtFrames.ExtData.res_t'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule` (same contribution).
Other imports: `Mathlib`.
