# `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.solution hR K`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Existence of a dominating discrete valuation ring (Krull–Akizuki type statement): for a noetherian
local domain `R` that is not a field, with fraction field `K`, there is a valuation subring `V` of
`K` that is a discrete valuation ring, contains (the image of) `R`, and dominates `R`: an element
`r : R` lies in the maximal ideal of `R` if and only if its image lies in the non-units of `V`. The
proof term applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates` (same contribution).
All modules also import `Mathlib`.
