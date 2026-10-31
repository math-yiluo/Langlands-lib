# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso`

## Source

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands.
  - FLT line 21: `p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso.solution` becomes `exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso.solution X X' g ι U hU c`. `p2m_exact_reverting` reverts the whole local context and elaborates the term against the reverted goal; `exact` applies the same term to the same hypotheses in the same order (`_` for anonymous hypotheses such as instances).
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `AlgebraicGeometry.Scheme.Modules.exists_pullback_glueOfCocycle_iso`

## Statement

Let `g : X' ⟶ X`, let `U : ι → X.Opens` cover `X` and let `c` be a unit cocycle on `U`. Then there is an isomorphism `φ` from the pullback along `g` of `glueOfCocycle c` to `glueOfCocycle (c.comap g)` (glued on the opens `g ⁻¹ᵁ U i`) such that, for every `i`, `φ` sends the pulled-back frame `pullbackLocalSection g (glueFrame c i)` (from `Def_AlgebraicGeometry_ModulesPullbackLocalSection`) to `glueFrame (c.comap g) i`.

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`, `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso`.
