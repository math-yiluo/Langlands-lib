# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 3 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry`: namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry` dropped.
- 6 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback`. Statement. `AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback`: if `p : X' ⟶ X` is the base
change of `f : X ⟶ Spec R` along `Spec A ⟶ Spec R`, a presentation `𝔓` of `M` over `f` pulls back to a
presentation of `p^* M` over `f'` with the pulled-back sections, whose morphism to `ℙᴺ_A` lies over `𝔓.toProj`
(via `ProjSpace.map R A N`) and forms a pullback square.

Proof. The morphism `X' ⟶ ℙᴺ_A` is induced by `p ≫ 𝔓.toProj` and `f'` through the pullback square of
projective spaces (ported `ProjSpace.isPullback_map`); the preimages of the charts are the pulled-back
charts (ported `ProjSpace.map_preimage_basicOpen_X`), on which the pulled-back sections remain frames
(ported `Scheme.Modules.bijective_smul_unit_app_of_bijective_smul`), and the ratio relations pull back.
Pasting pullback squares gives the last conclusion.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.toProj'`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.toProj'_map`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.toProj'_π`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.isPullback_toProj'`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.preimage_chart`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.σ'`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.presheaf_map_congr`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.eta`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.eta_smul`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.eta_resTop`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.ratio_pulled`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.awayToSection_mk_congr`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.presheaf_map_congr'`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.presheaf_map_map_eq`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.map_app_ratio`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.toProj'_app_ratio`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.resTop_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.AlgebraicGeometry.Scheme.Modules.PresBC.baseChange`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul` (Library).
Other imports: `Mathlib`.
