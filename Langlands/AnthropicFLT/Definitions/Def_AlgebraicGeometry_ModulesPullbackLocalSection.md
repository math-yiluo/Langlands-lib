# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`

## Source

Port of `Definitions/Def_AlgebraicGeometry_ModulesPullbackLocalSection.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: apart from the renames described under “Names changed by the Library” below, the declarations, statements and proofs are the FLT text.

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
- theorem `pullback_hom_extFLT`

## Dependencies

Ported FLT modules imported: none.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- it declares `AlgebraicGeometry.Scheme.Modules.pullback_hom_extFLT` (FLT `AlgebraicGeometry.Scheme.Modules.pullback_hom_ext`).

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
