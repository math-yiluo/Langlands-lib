# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `P2mGrStruct`). Generic lemmas: if `f` is surjective with kernel `J • ⊤` then `J • ⊤ = ⊥` in the
target (`pow_smul_top_eq_bot`); linear maps preserve `J • ⊤` (`map_mem_smul_top`); `a ∈ J` maps `J^n • ⊤` into
`J^(n+1) • ⊤` (`smul_mem_pow_succ_smul_top`). The structure `Sys` bundles the hypotheses. Then `I^(n+1)` kills
`F n` on affines (`pow_smul_top`, `smul_eq_zero_of_mem`), `g m ∈ I` (`g_mem`), and the image of `j k` lies in
`I^(k+1) • F(k+1)` (`j_mem_pow`). For `x ∈ K k(U)` choose a lift `y ∈ F(k+2)(U)` of `j k x` along `φ (k+1)`
(`exists_lift`); then `g m • y` lies in the image of `j (k+1)` (`smul_lift_mem_range`) and does not depend on the
lift (`smul_lift_eq`), so `thetaFun m k U x` is its unique preimage (`j_thetaFun`). It is additive, `A`- and
`Γ(V, U)`-linear and compatible with restriction (`thetaFun_add`, `thetaFun_smul`, `thetaFun_sectionSmul`,
`thetaFun_res`), giving `theta m k : AffHom (K k) (K (k+1))` (`theta_app`, `j_theta`). The `theta m` commute
(`theta_comm`, both sides map to `g m g m' • y'` for a lift `y'` two steps up). Surjectivity: an element of
`I^(k+1) • F(k+2)` multiplied by `g m` lies in `j (k+1)` of the range of `theta m k` (`smul_mem_map_range`), so
`I^(k+2) • F(k+2) = image of j (k+1)` is contained in the image of `⨆ m, range (theta m k)`
(`pow_smul_top_le_map_iSup`); injectivity of `j (k+1)` then gives `⨆ m, range (theta m k) = ⊤`
(`iSup_range_theta`). `solution` builds the `Sys` and returns `theta`, `j_theta`, `theta_comm`, `iSup_range_theta`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.pow_smul_top_eq_bot`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.map_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.smul_mem_pow_succ_smul_top`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.pow_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.smul_eq_zero_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.g_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.j_mem_pow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.sections_smul_comm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.smul_lift_mem_range`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.smul_lift_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.exists_lift`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.thetaFun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.j_thetaFun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.thetaFun_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.thetaFun_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.thetaFun_sectionSmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.thetaFun_res`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.theta_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.j_theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.theta_comm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.smul_mem_map_range`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.pow_smul_top_le_map_iSup`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.P2mGrStruct.Sys.iSup_range_theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
