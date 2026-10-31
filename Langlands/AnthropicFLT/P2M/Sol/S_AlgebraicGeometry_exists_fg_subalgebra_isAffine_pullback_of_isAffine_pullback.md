# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback`

Ported module of the proof submitted by task `8b63dc1d-84d3-43fa-a1d5-9657a89c8df1` (descent of separatedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. Index by the finitely generated subalgebras containing `s` (directed, nonempty, exhausting `A`); by
`SubalgebraStages.nonempty_isLimit_cone` (ported by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`) the base change to `Spec A` is the limit
of the base changes to the `Spec T`, with affine transition maps. Mathlib's
`Scheme.exists_isAffine_of_isLimit` (if the limit of such a system of qcqs schemes is affine, some stage is
affine) gives the stage.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SubalgebraStages` (ported by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone` (ported by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`).
All modules also import `Mathlib`.
