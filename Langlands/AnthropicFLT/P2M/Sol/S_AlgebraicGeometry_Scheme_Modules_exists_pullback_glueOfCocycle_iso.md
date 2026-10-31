# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands.
  - FLT line 15: `p2m_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry"` becomes `open CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry`.
- No other change: the declarations, statements and proofs are the FLT text.

## Mathematical content

`solution` states: for a morphism `g : X' ⟶ X`, opens `U i` covering `X` and a unit cocycle `c` on them,
there is an isomorphism `φ : g^*(glueOfCocycle c) ≅ glueOfCocycle (c.comap g)` (the cocycle `c.comap g`
lives on the opens `g⁻¹(U i)`) that sends the pulled-back frame `pullbackLocalSection g (glueFrame c i)` to
`glueFrame (c.comap g) i` for every `i`.

Proof as implemented: the preimages `g⁻¹(U i)` cover `X'`. The sections
`e i = pullbackLocalSection g (glueFrame c i)` are frames on `g⁻¹(U i)` by the LB2 lemma
`IsFrameOn.pullbackLocalSection`. On `g⁻¹(U i) ⊓ g⁻¹(U j)` the restriction of `e j` is
`(c.comap g).u i j • (restriction of e i)`: restriction commutes with `pullbackLocalSection`
(`map_homOfLE_pullbackLocalSection`), the frames of the glued module satisfy the same relation with `c.u i j`
(`map_glueFrame_eq_smul`), and `pullbackLocalSection` turns scalar multiplication by a function into
multiplication by its pullback (`pullbackLocalSection_smul`). The companion theorem
`exists_iso_glueOfCocycle_app_eq_glueFrame`, applied to the cover `g⁻¹(U i)`, the cocycle `c.comap g` and the
frames `e i`, gives `φ`.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection`.
