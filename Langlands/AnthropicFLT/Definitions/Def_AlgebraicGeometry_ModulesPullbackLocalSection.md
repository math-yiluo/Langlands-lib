# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`

## Source

Port of `Definitions/Def_AlgebraicGeometry_ModulesPullbackLocalSection.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- def `pullbackLocalSection`
- lemma `pullbackLocalSection_def`
- lemma `pullbackLocalSection_add`
- lemma `pullbackLocalSection_zero`
- lemma `pullbackLocalSection_neg`
- lemma `pullbackLocalSection_sub`
- lemma `pullbackLocalSection_sum`
- lemma `pullbackLocalSection_smul`
- lemma `map_pullbackLocalSection`
- lemma `map_homOfLE_pullbackLocalSection`
- lemma `pullbackLocalSection_app`
- lemma `app_pullbackLocalSection`
- lemma `homEquiv_symm_app_pullbackLocalSection`
- lemma `counit_app_pullbackLocalSection`
- theorem `pullback_hom_ext`

## Dependencies

Ported FLT modules imported: none.
