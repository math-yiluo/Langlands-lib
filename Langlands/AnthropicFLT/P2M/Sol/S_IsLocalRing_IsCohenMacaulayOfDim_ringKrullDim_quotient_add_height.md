# `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `CMDimFormula`). The inequality `dim (R ⧸ p) + height p ≤ dim R` holds in every
noetherian local ring (`ringKrullDim_quotient_add_height_le`). For the reverse, induct on the height
`n` of `p` (`le_ringKrullDim_quotient_add`): if `n > 0`, choose a regular element in `p` (depth is
positive), pass to the quotient, which is Cohen–Macaulay of dimension `d - 1`, and use the depth
drop by one; `depth_eq_of_linearEquiv` and the arithmetic lemmas `enat_eq_of_add_one_eq`,
`withBot_eq_of_add_one_eq` handle the bookkeeping.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.CMDimFormula.ringKrullDim_quotient_add_height_le`
- theorem `P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.CMDimFormula.depth_eq_of_linearEquiv`
- theorem `P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.CMDimFormula.enat_eq_of_add_one_eq`
- theorem `P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.CMDimFormula.withBot_eq_of_add_one_eq`
- theorem `P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.CMDimFormula.le_ringKrullDim_quotient_add`
- theorem `P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Patching_CohenMacaulayOfDim` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_depth_quotSMulTop_succ_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_depth_quotient_eq_depth` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Ideal_height_map_quotientMk_span_singleton_add_one` (same contribution).
Other imports: `Mathlib`.
