# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands.
  - FLT line 15: `p2m_open "CategoryTheory Opposite AlgebraicGeometry TopologicalSpace CategoryTheory.MonoidalCategory"` becomes `open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace CategoryTheory.MonoidalCategory`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `pullbackLocalSection_openImmersion`
- theorem `pullbackComp_hom_app_app_pullbackLocalSection`
- theorem `isFrameOn_of_map`
- theorem `bijective_smul_congr`
- theorem `isFrameOn_pullbackLocalSection_congr`
- theorem `restrict_map_unit`
- theorem `isFrameOn_restrict_unit`
- theorem `image_preimage_eq_of_le`
- theorem `isFrameOn_of_restrict_unit`
- theorem `iso_inv_hom_app_apply`
- theorem `isFrameOn_of_map_iso`
- theorem `isFrameOn_pullbackLocalSection_congr'`
- theorem `exists_iso_of_isFrameOn_self`
- theorem `isFrameOn_pullbackLocalSection_self`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal`.
