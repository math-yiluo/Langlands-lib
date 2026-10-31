# `Langlands.AnthropicFLT.P2M.Sol.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof: convert `ringKrullDim R ≤ 1` to `Ring.KrullDimLE 1 R`, apply
`Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite` to `B` (noetherian and
`Ring.DimensionLEOne`; the finite-length part is discarded), and convert `Ring.DimensionLEOne B`
(through the instance `Ring.KrullDimLE 1 B`) back to `ringKrullDim B ≤ 1`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite` (same contribution).
All modules also import `Mathlib`.
