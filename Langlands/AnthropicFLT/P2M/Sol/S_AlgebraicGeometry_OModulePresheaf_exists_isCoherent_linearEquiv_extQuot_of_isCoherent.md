# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- `p2m_export` also exports from namespaces that contain only private declarations of this module (`EP3Geo`), which Lean does not register as namespaces; Lean's `export` rejects them, so each of them is registered by an empty block `namespace N end N` right after the options.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent`.

Proof: construction of the coherent sheaf `Ext¹(H, K)` from the presentation models on affines.

- `EP3Alg` (algebra). `EQ p N` is the presentation model `Hom(ker p, N) / (maps extending to B^r)`; `presBC` is the
  base change of a presentation (`presBC_apply`, `presBC_apply_algebraMap`), and `linz` linearizes a semilinear map
  out of `B^r` (`single_eq_algebraMap_single`, `linz_algebraMap`). `Phi` is the comparison isomorphism between two
  presentations from the ported theorem `LinearMap.exists_linearEquiv_extQuot_forall_comp_eq_of_surjective`
  (`Phi_mk`, `exists_lift`, `kerLift`, `kerLift_coe`, `Phi_mk'`), coherent under composition (`Phi_trans`,
  `Phi_self`, `Phi_Phi`, `Phi_symm_apply`). Over a noetherian `B` and flat `B'`, `Tmap` is the base-change map of
  the ported theorem `LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective` (`presBC_surjective`, `gBC`,
  `gBC_coe`, `Tmap_isBaseChange`, `Tmap_exists_compat`, `Tmap_mk`), and `rho` composes it with `Phi` to compare
  arbitrary presentations over `B` and `B'` (`Phi_rho`, `rho_mk`, `rho_smul`, `Tmap_Phi`, `rho_Phi`, `Phi_rho_eq`),
  transitively in towers (`rho_comp`). For a localization `B'` of `B`, `rho` is a localization map
  (`rho_isLocalizedModule`); `EQ` is finite for finite `N` (`finite_EQ`); restriction between affine opens is flat
  (`flat_of_affineOpens_le`).
- `EP3Geo` (geometry, `P` locally noetherian). On each affine `W` choose a presentation `pres H W` of `H(W)`
  (`RW`, `noeth`, `exists_pres`, `rk`, `pres`, `pres_surjective`) and put `E W = EQ (pres H W) (K(W))` (`modA`).
  Restriction maps (`algOf`, `modOf`, `towOf`, `mu`, `mu_apply`, `flatOf`; `mu_isBaseChange` by quasi-coherence;
  `map_refl`, `map_map`, `map_algebraMapA`) induce `resΓ` and `res` on `E` (`resΓ_def`, `res_apply`), which are
  semilinear, functorial, and localizations on basic opens (`resΓ_smul`, `resΓ_refl`, `resΓ_comp`,
  `resΓ_isLocalizedModule`), with `E W` finite (`finite_E`). `main` applies the ported theorem
  `exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis` with `B` the set of all affine opens to get a
  coherent quasi-coherent `X` with `X(W) ≅ E W` compatibly with restriction.
- `EP3Clause`: the compatibility clause holds algebraically (`clause_alg`, via `rho`), and `upgradeEquiv` upgrades
  an `A`-linear isomorphism commuting with `Γ(P, W)` to a `Γ(P, W)`-linear one (`upgradeEquiv_apply`,
  `upgradeEquiv_symm_apply`).

`solution`: `ε W r p hp` is the upgraded `e W` followed by `Phi` from `pres H W` to `p`; the compatibility with
restriction follows from `e_res`, `resΓ_def` and `clause_alg`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.EQ`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.presBC`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.presBC_apply`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.presBC_apply_algebraMap`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.linz`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.single_eq_algebraMap_single`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.linz_algebraMap`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_mk`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.exists_lift`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.kerLift`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.kerLift_coe`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_mk'`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_trans`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_self`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_Phi`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_symm_apply`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.presBC_surjective`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.gBC`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.gBC_coe`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Tmap`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Tmap_isBaseChange`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Tmap_exists_compat`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Tmap_mk`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.rho`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_rho`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.rho_mk`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.rho_smul`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Tmap_Phi`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.rho_Phi`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.Phi_rho_eq`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.rho_comp`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.rho_isLocalizedModule`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.finite_EQ`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Alg.flat_of_affineOpens_le`
- abbrev `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.RW`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.noeth`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.exists_pres`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.rk`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.pres`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.pres_surjective`
- abbrev `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.E`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.modA`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.algOf`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.modOf`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.towOf`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.mu`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.mu_apply`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.flatOf`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.mu_isBaseChange`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.map_refl`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.map_map`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.map_algebraMapA`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.resΓ`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.resΓ_def`
- private def `EP3Geo.res`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.res_apply`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.resΓ_smul`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.resΓ_refl`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.resΓ_comp`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.resΓ_isLocalizedModule`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.finite_E`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Geo.main`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Clause.clause_alg`
- def `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Clause.upgradeEquiv`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Clause.upgradeEquiv_apply`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.EP3Clause.upgradeEquiv_symm_apply`
- theorem `EP3Geo.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis` (same contribution).
Other imports: `Mathlib`.
