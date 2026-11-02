# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 6 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop`. Statement. `AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop`: for a quasi-compact, quasi-separated
`X ⟶ Spec k` over a field with `k → Γ(X, ⊤)` bijective, the base change to any `k`-algebra `A` has
`A → Γ(X_A, ⊤)` bijective.

Proof (flat base change of global sections over a field). Sections over affine opens of `X_A` are
`A ⊗_k` the sections of `X` (`toSec`, `isPushout_toSec_app`, section `Over`: `baseChangeSections`,
`isPushout_sections`, `bijective_baseChangeSections`). Section `Sheaf` and `Cech`: global sections are the
equalizer of the finite Čech diagram of a finite affine cover (quasi-compact) with affine-covered
intersections (quasi-separated) (`exists_finite_affine_cover`, `cechDiff`, `exact_resPi_cechDiff`); `A ⊗_k -`
is exact (`k` a field), so `Γ(X_A) = A ⊗_k Γ(X) = A ⊗_k k = A` (`bijective_baseChangeSections_top`, section
`Final`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.bc`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.toSec`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.appLE_top_top`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.toSec_top`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.toSec_map`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.toSecA`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.appLE_congrHom`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.toSec_app`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.isPushout_toSec_app`
- scoped instance `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.secAlgebra`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.algebraMap_sec`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.resAlgHom`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.resAlgHom_apply`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.res`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.res_apply`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.XA`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.fstA`
- scoped instance `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.secAlgebraK`
- scoped instance `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.isScalarTower_secK`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.appAlgHom`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.appAlgHom_apply`
- scoped instance `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.appAlgebra`
- scoped instance `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.isScalarTower_app`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.baseChangeSections_tmul`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.preimage_mono`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.res_baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.isPushout_sections`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.baseChangeSections_eq_equiv`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.bijective_baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.sections_ext`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.sections_glue`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.bijective_of_flat_of_exact`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.resPi`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.injective_resPi`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.piRight_lTensor_resPi`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.injective_baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.res_res`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.exists_finite_affine_cover`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.cechDiff`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.exact_resPi_cechDiff`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.bijective_baseChangeSections_top`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.isPushout_appTop`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0.bijective_appTop_snd`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
