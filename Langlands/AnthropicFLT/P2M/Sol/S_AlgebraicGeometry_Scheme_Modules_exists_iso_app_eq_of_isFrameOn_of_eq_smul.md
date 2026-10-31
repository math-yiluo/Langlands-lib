# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 13: `p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace"` becomes `open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace`.
  - FLT line 14: `p2m_open "AlgebraicGeometry N.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"` becomes `open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 17: `p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.IsFrameOn"` becomes `export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.IsFrameOn)`.
  - FLT line 19: `p2m_open "AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `map_le_refl`
- theorem `isUnit_of_isFrameOn_smul`
- def `theta`
- theorem `ihomEval_theta`
- theorem `eq_theta`
- theorem `map_theta`
- theorem `theta_indep`
- theorem `main`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesIhomSections`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top`.
