# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range`.

Proof (namespace `P2mAffCokerSol`). For an affine-indexed homomorphism `h : AffHom H G` the cokernel presheaf
is built directly. `N h U` is the submodule of `G(U)` of sections whose restriction to every affine open
`W ≤ U` lies in the range of `h.app W`; it is stable under scalars (`N_smul_mem`) and restriction (`N_res`),
and on an affine open it equals the range of `h.app` (`N_eq_range`, using naturality of `h`). `Q h` is the
presheaf `U ↦ G(U) ⧸ N h U` with the induced restrictions and `Γ(P, U)`-module structure
(`qModuleSections`), and `ρ h : AffHom G (Q h)` is the quotient map, surjective on affines (`ρ_surjective`)
with kernel the range of `h.app` (`ker_ρ`). `Q h` is coherent when `G` is (quotients of finite modules are
finite, `isCoherent_Q`), and quasi-coherent when `H` and `G` are (`isQuasicoherent_Q`): the localisation
property of `G` lifts elements of `Q(D(f))`, and an element of `G(U)` mapping to `0` in `Q(D(f))` is, on
`D(f)`, in the range of `h`; lifting that preimage to `U` with the property of `H` and comparing with the
injectivity property of `G` shows that `f^(m+n)` times it lies in the range of `h.app U`. `main` packages
these facts and `solution` is `P2mAffCokerSol.main h hHq hGq`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.N`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.mem_N`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.range_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.N_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.N_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.N_eq_range`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.qModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.Q`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.Q_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.Q_res_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.Q_smul_mk`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.ρ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.ρ_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.ρ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.ker_ρ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.isCoherent_Q`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.isQuasicoherent_Q`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.P2mAffCokerSol.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
