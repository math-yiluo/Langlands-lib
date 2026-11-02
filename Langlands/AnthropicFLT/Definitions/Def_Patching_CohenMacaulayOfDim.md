# `Langlands.AnthropicFLT.Definitions.Def_Patching_CohenMacaulayOfDim`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Patching_CohenMacaulayOfDim.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

`IsLocalRing.IsCohenMacaulayOfDim R d` (a `Prop`) for a local ring `R` and `d : ℕ`: `R` has
Krull dimension `d` and depth `Module.depth R R = d` (with FLT's `Module.depth` from
`Def_Patching_SystemTypes`). The lemmas `ringKrullDim_eq` and `depth_eq` project the two
conditions.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `IsLocalRing.IsCohenMacaulayOfDim`
- lemma `IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_eq`
- lemma `IsLocalRing.IsCohenMacaulayOfDim.depth_eq`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Patching_SystemTypes` (same contribution).
Other imports: `Mathlib`.
