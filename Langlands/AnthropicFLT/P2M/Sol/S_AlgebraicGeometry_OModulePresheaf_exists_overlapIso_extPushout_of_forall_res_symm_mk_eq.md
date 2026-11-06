# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq`.

Proof (namespace `X1bOverlapSol`): when two charts carry the same `Ext¹` class on their overlap, their pushout
extensions are isomorphic over the overlap.

- `Core` (algebra): given presentations `p`, `p'` of `M`, a map `γ` with `p' ∘ γ = p` and `φ : B^r → N` with
  `δ' ∘ γ = δ + φ` on `ker p` (`gamma_mem`), `coreMap` is the map `ExtPushout p δ → ExtPushout p' δ'` with
  `inl n ↦ inl n` and `inr v ↦ inr (γ v) − inl (φ v)` (`coreMap_inl`, `coreMap_inr`); it commutes with `proj`
  (`proj_coreMap`) and is injective, and surjective when `p` is (`coreMap_injective`, `coreMap_surjective`).
- Helpers: extensionality of additive maps out of `ExtPushout` (`addHom_ext`), expansion in the standard basis
  (`pi_eq_sum_single`, `apply_eq_sum_single`, `map_single`, `lin`, `lin_apply`, `lin_single`); restriction of `γ`
  and `φ` to smaller opens (`ρ`, `ρ_ρ`, `ρ_refl`, `gammaRes`, `gammaRes_apply`, `phiRes`, `phiRes_apply`,
  `gammaRes_res`, `phiRes_res`, `gammaRes_refl`, `phiRes_refl`, `port_gammaRes_rho`, `port_phiRes_rho`,
  `map_homOfLE_refl_apply`).
- `exists_lift_corr`: on the affine overlap `U_i ∩ U_j`, equality of the classes of `δ i` and `δ j` (hypothesis
  `hδ` with the compatibility `hXf` of `X`) yields `γ` and `φ` as in `Core`; `prU_gammaRes` and `deltaU_gammaRes`
  restrict these relations to every affine `W` inside the overlap.
- `rebase` views a `Γ(P, W)`-linear map as `A`-linear (`rebase_apply`, `coe_rebase`).

`solution`: `u i j W hj` is the rebased `coreMap` built from the restricted `γ` and `φ`; it is bijective, semilinear
and compatible with `res` (checked on `inl` and `inr` with `addHom_ext`, `res_inl`, `res_inr`), maps `inl` to `inl`
and commutes with `proj`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.gamma_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.coreMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.coreMap_inl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.coreMap_inr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.proj_coreMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.coreMap_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.coreMap_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.addHom_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.pi_eq_sum_single`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.apply_eq_sum_single`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.map_single`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.lin`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.lin_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.lin_single`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.ρ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.ρ_ρ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.ρ_refl`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.gammaRes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.gammaRes_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.phiRes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.phiRes_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.gammaRes_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.phiRes_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.gammaRes_refl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.phiRes_refl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.map_homOfLE_refl_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.exists_lift_corr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.port_gammaRes_rho`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.port_phiRes_rho`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.prU_gammaRes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapSol.deltaU_gammaRes`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapAsm.rebase`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapAsm.rebase_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.X1bOverlapAsm.coe_rebase`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_LinearMap_ExtPushout` (same contribution).
Other imports: `Mathlib`.
