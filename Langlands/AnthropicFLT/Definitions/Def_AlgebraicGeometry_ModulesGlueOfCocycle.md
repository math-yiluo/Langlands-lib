# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`

## Source

Port of `Definitions/Def_AlgebraicGeometry_ModulesGlueOfCocycle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

The file builds the sheaf of modules glued from a unit cocycle. For a family of opens `U : ι → X.Opens`, a
`UnitCocycle U` is a family `u i j : Γ(X, U i ⊓ U j)` with `u i i = 1` and `u i j * u j k = u i k` on triple
overlaps (restrictions written with `GlueOfCocycle.rO`). `glueOfCocycle c : X.Modules` has as sections over `T`
the families `x i : Γ(X, T ⊓ U i)` with `x i = u i j * x j` on `T ⊓ U i ⊓ U j` (`GlueOfCocycle.families`), and
`glueFrame c i` is a section over `U i` that is a frame there (`isFrameOn_glueFrame`) with transition
`map_glueFrame_eq_smul`. The file makes no hypothesis that the `U i` cover `X`.

Declarations, with their original FLT names (no new definitions or statements are introduced). In namespace
`AlgebraicGeometry.Scheme.Modules.GlueOfCocycle`:

- abbrev `rO`
- theorem `rO_rO`
- theorem `rO_irrel`
- theorem `rO_refl`
- theorem `rO_rO_self`
- theorem `rO_bijective_of_le_le`

In namespace `AlgebraicGeometry.Scheme.Modules`:

- structure `UnitCocycle`

In namespace `AlgebraicGeometry.Scheme.Modules.UnitCocycle`:

- theorem `cocycle_le`
- theorem `mul_symm`
- theorem `isUnit`
- def `trivial`
- def `mul`
- def `twist`
- def `comap`

In namespace `AlgebraicGeometry.Scheme.Modules.GlueOfCocycle`:

- theorem `leTi`
- theorem `leTj`
- theorem `leij`
- def `families`
- theorem `mem_families`
- unnamed instance `SMul Γ(X, T) (families c T)`
- theorem `smul_val`
- unnamed instance `Module Γ(X, T) (families c T)`
- def `resFam`
- theorem `resFam_val`
- def `preGlue`
- instance `instModulePreGlue`
- theorem `preGlue_map_smul`
- def `preGlueMod`
- theorem `preGlue_isSheaf` (with the FLT-local option `set_option maxHeartbeats 400000 in`)

In namespace `AlgebraicGeometry.Scheme.Modules`:

- def `glueOfCocycle`
- theorem `glueOfCocycle_sections_eq`
- theorem `glue_map_val`
- theorem `glue_smul_val`
- def `glueComponent`
- theorem `glueComponent_apply`
- theorem `glue_ext`
- theorem `glueComponent_transition`
- theorem `glueComponent_map`
- theorem `glueComponent_smul`
- def `glueMk`
- theorem `glueComponent_glueMk` (`@[simp]`)
- def `glueFrame`
- theorem `glueComponent_glueFrame`
- theorem `glueComponent_glueFrame_self`
- theorem `isFrameOn_glueFrame`
- theorem `map_glueFrame_eq_smul`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`.
