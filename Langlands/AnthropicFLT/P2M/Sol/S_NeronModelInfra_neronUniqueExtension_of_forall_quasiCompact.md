# `Langlands.AnthropicFLT.P2M.Sol.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - FLT `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra"`: namespace `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra` dropped.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `NeronModelInfra.NeronUniqueExtensionOfQC`). Injectivity for arbitrary smooth `t`
follows from injectivity on an affine cover of `T`. For surjectivity, restrict the generic-fibre
morphism to the members of the affine cover of `T` (`chartRestrict`), extend on each (affine,
hence quasi-compact) member, and compare the extensions on overlaps by injectivity on the pulled
back charts (`fibreShift`, `exists_pulledChart_compare`); the extensions glue
(`pulledChart_fst_glue_eq`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.fibreShift`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.fibreShift_fst`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.fibreShift_snd`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.fibreShift_comp`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.fibreShift_congr`
- def `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.chartRestrict`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.chartRestrict_coe`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.genericFibreRestrict_chartRestrict`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.chartSolution_restrict_eq`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.exists_pulledChart_compare`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC.pulledChart_fst_glue_eq`
- theorem `P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated` (same contribution).
Other imports: `Mathlib`.
