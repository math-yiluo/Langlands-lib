# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`.

Proof (namespace `GlueFromBasisSol`): a presheaf given on a downward-closed basis `B` of affine opens extends to a
coherent quasi-coherent FLT presheaf.

- `GData` bundles the data (`res_res`, `res_congr`; basic opens of members are members, `bo`, `bo_coe`, `bo_le`).
  For an open `U`, `Mem U` is the set of members of `B` inside `U` and `fam U` the `R`-module of compatible families
  `(x_W)_{W ∈ Mem U}` (`mem_fam_iff`), a `Γ(V, U)`-module through restriction (`toMem`, `toMem_algebraMap`,
  `map_toMem`, `famSMul`, `famModule`), with restrictions `famRes`. This defines the FLT presheaf `G` (`G_obj`,
  `G_res_coe`, `G_smul_coe`, `G_ext`). On a member `W`, evaluation at `W` is an isomorphism
  `e W : G(W) ≅ M W` (`ev`, `lf`, `ev_lf`, `lf_ev`, `e_apply`, `e_symm_apply_coe`), semilinear and compatible
  with restriction (`e_smul`, `e_res`, `coe_eq_e_res`).
- Localization structure: viewing the `M W` (`MO`, `instACG_MO`, `instMod_MO`, `MO_smul_def`) and their
  restrictions (`resO`, `resO_apply`, `resO_resO`) as modules over `Γ(V, O)`, restriction to a basic open is a
  localization (`boO`, `boO_coe`, `boO_le`, `boO_coe'`, `toMem_boO`, `isLocalizedModule_resO`, from hypothesis
  `hqc`). Every affine `U` has a finite cover by basic opens in `B` (`exists_cover`, `cm`, `cm_coe`, `boO_le_cm`,
  `boO_mono`), on which sections of `M` and of `G` are separated and glue (`MO_eq_zero_of_forall`,
  `MO_eq_of_forall`, `G_eq_zero_of_forall_cm`, `G_eq_of_forall_cm`, `MO_exists_of_compatible`,
  `G_exists_of_compatible`).
- Quasi-coherence and coherence: viewing `G` over smaller opens as `Γ(V, O)`-modules (`GO`, its instances,
  `GO_smul_coe`, `instTower_GO`, `GresO`, `GresO_coe`, `G_eq_zero_of_forall_boO`), restriction to basic opens of
  affines is a localization (`isLocalizedModule_GresO`, `GO_self_smul`), so `G` is quasi-coherent
  (`G_isQuasicoherent`); `G(W) ≅ M W` is finite on members (`G_finite_mem`, hypothesis `hfg`), hence `G` is coherent
  (`G_isCoherent`).
- Comparison with a quasi-coherent `F` (`FSide`): the analogous separation and gluing for `F` over basic covers
  (`eq_of_forall_isLocalizedModule_eq`, `FO`, `FresO`, `Fres₀` and their lemmas, `isLocalizedModule_FresO`,
  `isLocalizedModule_Fres₀`, `F_eq_of_forall_res_basicOpen_eq`, `F_exists_of_forall_res_eq`).
- Maps into `G` (`ClauseB`): compatible `ϑ W : F(W) → M W` define `inHom : F → G` by
  `y ↦ (ϑ W (y|_W))_W` (`inApp`, `inApp_coe`, `e_inHom_app`), unique by `affHom_ext` (`existsUnique_in`;
  `affHom_naturality_apply`).
- Maps out of `G` (`ClauseA`): for compatible `θ W : M W → F(W)`, a section `t` of `G` over an affine `U` has a
  unique `m ∈ F(U)` restricting to `θ W (t_W)` on every member `W ⊆ U` (`cov`, `cov_span`, `cov_mem`, `covMem`,
  `res_theta_eq`, `out_exists`, `out_unique`, by gluing in `F`); this defines `outHom : G → F` (`outFun`,
  `outFun_spec`, `outFun_eq`, `outApp`, `outHom_app_member`), unique (`existsUnique_out`).

`solution` builds the `GData` and returns `G`, `e` and these properties.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.res_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.res_congr`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.bo`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.bo_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.bo_le`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.Mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.fam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.mem_fam_iff`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.toMem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.toMem_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.map_toMem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.famSMul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.famModule`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.famRes`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_res_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_smul_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_ext`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.ev`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.lf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.ev_lf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.lf_ev`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.e`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.e_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.e_symm_apply_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.e_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.e_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.coe_eq_e_res`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.MO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.instACG_MO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.instMod_MO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.MO_smul_def`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.resO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.resO_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.resO_resO`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.boO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.boO_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.boO_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.boO_coe'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.toMem_boO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.isLocalizedModule_resO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.exists_cover`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.cm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.cm_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.boO_le_cm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.boO_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.MO_eq_zero_of_forall`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.MO_eq_of_forall`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_eq_zero_of_forall_cm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_eq_of_forall_cm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.MO_exists_of_compatible`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_exists_of_compatible`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.GO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.instACG_GO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.instModSelf_GO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.instMod_GO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.GO_smul_coe`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.instTower_GO`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.GresO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.GresO_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_eq_zero_of_forall_boO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.isLocalizedModule_GresO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.GO_self_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_isQuasicoherent`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_finite_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.G_isCoherent`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.eq_of_forall_isLocalizedModule_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.FO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.instACG_FO`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.instMod_FO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.FO_smul_def`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.FresO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.FresO_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.Fres₀`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.Fres₀_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.isLocalizedModule_FresO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.isLocalizedModule_Fres₀`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.F_eq_of_forall_res_basicOpen_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.F_exists_of_forall_res_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.affHom_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.affHom_naturality_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.inApp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.inApp_coe`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.inHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.e_inHom_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.existsUnique_in`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.cov`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.cov_span`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.cov_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.covMem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.res_theta_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.out_exists`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.out_unique`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.outFun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.outFun_spec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.outFun_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.outApp`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.outHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.outHom_app_member`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData.existsUnique_out`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top` (same contribution).
Other imports: `Mathlib`.
