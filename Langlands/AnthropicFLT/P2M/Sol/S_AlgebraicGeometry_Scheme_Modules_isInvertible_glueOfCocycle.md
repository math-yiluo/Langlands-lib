# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands.
  - FLT line 11: `p2m_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry"` becomes `open CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry`.
- No other change: the declarations, statements and proofs are the FLT text.

## Mathematical content

`solution` states: if the opens `U i` cover `X` (`⨆ i, U i = ⊤`) and `c` is a unit cocycle on them (FLT
`Scheme.Modules.UnitCocycle`, ported module `Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`), the
glued module `glueOfCocycle c` is invertible in FLT's sense.

Proof as implemented: by `isInvertible_of_forall_exists_isFrameOn` it suffices to give, for every point
`x`, a frame on an open containing `x`. Choose `i` with `x ∈ U i`; the section `glueFrame c i` is a frame on
`U i` by `isFrameOn_glueFrame` of the definition module.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn`.
