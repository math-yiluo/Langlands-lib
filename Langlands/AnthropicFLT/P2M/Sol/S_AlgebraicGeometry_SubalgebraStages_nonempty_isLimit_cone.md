# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. First, `A` with the inclusions is a colimit of the rings `S i` in `CommRingCat`
(`LimBC.nonempty_isColimit_ringCocone`): the forgetful functor reflects this colimit and, in types, it
is a filtered colimit because every element of `A` lies in some `S i` and two elements that agree in `A`
agree in a common larger stage. Since `Spec` turns colimits into limits, `specCone S` is a limit cone
(`LimBC.nonempty_isLimit_specCone`). The limit property of `cone S f` is then checked by hand: a cone over
the stages gives one morphism to `X` (all first projections agree, by directedness) and a cone over the
`Spec (S i)`, hence a morphism to `Spec A`; these define the lift into the pullback, and uniqueness
follows from `pullback.hom_ext` and the uniqueness for `specCone`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.ringDiagram`
- def `P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.ringCocone`
- theorem `P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.nonempty_isColimit_ringCocone`
- theorem `P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.specCone_eq`
- theorem `P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.nonempty_isLimit_specCone`
- theorem `P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SubalgebraStages`.
All modules also import `Mathlib`.
