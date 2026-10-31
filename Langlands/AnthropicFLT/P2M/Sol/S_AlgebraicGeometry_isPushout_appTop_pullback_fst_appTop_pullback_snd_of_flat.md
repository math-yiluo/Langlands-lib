# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 6 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text (including the FLT
  `set_option synthInstance.maxHeartbeats 1600000 in` and `set_option maxHeartbeats 6400000 in`
  before `solution`).

## Content

Proof of flat base change for global sections (namespace `FBC0`, inside a `noncomputable section`).
Let `X_A = X ×_k Spec A` with projection `fstA : X_A ⟶ X`.

- Affine case: for an affine open `U` of `X`, the square `k → Γ(X, U)`, `A → Γ(X_A, fstA⁻¹U)` is a
  pushout of rings (`isPushout_toSec_app`), i.e. the `A`-algebra map
  `baseChangeSections : A ⊗_k Γ(X, V) → Γ(X_A, fstA⁻¹V)` is bijective for affine `V`
  (`bijective_baseChangeSections`). Scoped instances make the sections `k`-, `A`- and
  `Γ(X, V)`-algebras with the evident scalar towers.
- Sheaf property: sections over `V` covered by `W i` are determined by, and glue from, compatible
  restrictions (`sections_ext`, `sections_glue`); for a quasi-compact `V` the restriction map to a
  finite affine cover is injective, and tensoring with the flat `A` keeps it injective
  (`injective_baseChangeSections`).
- Global case (`bijective_baseChangeSections_top`): for `X` quasi-compact and quasi-separated, choose a
  finite affine cover `U i`; the sequence `0 → Γ(X) → ∏ Γ(U i) → ∏ Γ(U i ∩ U j)` is exact
  (`exact_resPi_cechDiff`), stays exact after `A ⊗_k –` (flatness), and a five-lemma type argument
  (`bijective_of_flat_of_exact`) with the bijection on the affine terms and injectivity on the
  quasi-compact intersections gives bijectivity on global sections.
- `isPushout_appTop` repackages this as the pushout square of the statement; `bijective_appTop_snd`
  is a corollary over a field (bijectivity of `appTop` is preserved by base change). `solution`
  applies `isPushout_appTop`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.bc`
- def `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.toSec`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.appLE_top_top`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.toSec_top`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.toSec_map`
- abbrev `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.toSecA`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.appLE_congrHom`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.toSec_app`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.isPushout_toSec_app`
- scoped instance `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.secAlgebra`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.algebraMap_sec`
- def `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.resAlgHom`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.resAlgHom_apply` (`@[scoped simp]`)
- abbrev `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.res`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.res_apply` (`@[scoped simp]`)
- abbrev `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.XA`
- abbrev `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.fstA`
- scoped instance `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.secAlgebraK`
- scoped instance `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.isScalarTower_secK`
- def `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.appAlgHom`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.appAlgHom_apply` (`@[scoped simp]`)
- scoped instance `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.appAlgebra`
- scoped instance `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.isScalarTower_app`
- def `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.baseChangeSections_tmul` (`@[scoped simp]`)
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.preimage_mono`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.res_baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.isPushout_sections`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.baseChangeSections_eq_equiv`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.bijective_baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.sections_ext`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.sections_glue`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.bijective_of_flat_of_exact`
- abbrev `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.resPi`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.injective_resPi`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.piRight_lTensor_resPi`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.injective_baseChangeSections`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.res_res`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.exists_finite_affine_cover`
- abbrev `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.cechDiff`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.exact_resPi_cechDiff`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.bijective_baseChangeSections_top`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.isPushout_appTop`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.FBC0.bijective_appTop_snd`
- theorem `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.solution`

## Dependencies

No ported FLT module is imported.
The module imports `Mathlib`.
