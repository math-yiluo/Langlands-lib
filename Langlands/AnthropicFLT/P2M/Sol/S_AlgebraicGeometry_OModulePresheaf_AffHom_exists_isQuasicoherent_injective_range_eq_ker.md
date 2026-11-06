# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker`.

Proof (namespace `P2mAffKerSol`), the kernel analogue of the cokernel construction in the solution of
`AffHom.exists_isQuasicoherent_surjective_ker_eq_range`. `L θ U` is the submodule of `G(U)` of sections whose
restriction to every affine `W ≤ U` is killed by `θ.app W`; it is stable under scalars and restriction, and on an
affine open it is the kernel of `θ.app` (`L_eq_ker`). `K θ` is the presheaf `U ↦ L θ U` and `ι θ` the inclusion,
injective with range the kernel of `θ` on affines (`ι_injective`, `range_ι`). `K θ` is coherent when `P` is locally
noetherian and `G` coherent (submodules of finite modules over noetherian rings, `isCoherent_K`), and
quasi-coherent when `G` and `F` are (`isQuasicoherent_K`): a kernel element on `D(f)` lifts, after a power of `f`,
to `y ∈ G(U)` whose image under `θ` vanishes on `D(f)`, so a further power of `f` puts it in the kernel;
injectivity is inherited from `G`. `main` packages these facts and `solution` is `P2mAffKerSol.main θ hGq hFq`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.L`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.mem_L`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.L_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.L_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.L_eq_ker`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.lModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.K_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.K_res_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.K_smul_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.ι`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.ι_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.ι_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.range_ι`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.isCoherent_K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.isQuasicoherent_K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.P2mAffKerSol.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
