# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 9: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry N.AlgebraicGeometry"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 14: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits`.
  - FLT line 19: `p2m_export "PresheafOfModules" "…"` with 13 names becomes `export _root_.PresheafOfModules (…)` with the same names.
  - FLT line 20: `p2m_open "PresheafOfModules"` becomes `open _root_.PresheafOfModules`.
  - FLT line 40: `p2m_export "AlgebraicGeometry" "…"` with 9 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 42: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 14 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names.
  - FLT line 44: `p2m_export "AlgebraicGeometry.Scheme.Modules" "…"` with 9 names becomes `export _root_.AlgebraicGeometry.Scheme.Modules (…)` with the same names.
  - FLT line 45: `p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- structure `TrivializationBelow`
- def `restrictRingCatSheafHom`
- def `restrictFunctor'`
- lemma `restrictFunctor'_eq`
- def `restrictFunctor'IsoPullback`
- lemma `image_preimage_of_le`
- def `gen₀`
- lemma `gen₀_spec`
- lemma `gen₀_bijective`
- lemma `gen₀_map`
- lemma `bijective_smul_map_eqToHom`
- def `trivializationBelow`
- theorem `exists_isFrameOn_of_pullback_iso_unit`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`.
