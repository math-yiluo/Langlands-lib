# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Quotients of regular local rings by an element of `𝔪 \ 𝔪²` (namespace `RegularQuotientEngine`).

- `isLocalRing_quotient_span_singleton`, generator counting (`exists_span_eq_maximalIdeal_ncard_le`,
  `one_le_spanFinrank_maximalIdeal_of_notMem_sq`, `spanFinrank_map_quotientMk_le_sub_one`,
  `spanFinrank_maximalIdeal_quotient_le_sub_one`), and finiteness of the Krull dimension of a
  noetherian local ring (`ringKrullDim_lt_top_of_isNoetherianRing_of_isLocalRing`,
  `exists_ringKrullDim_eq_natCast`).
- `isRegularLocalRing_quotient_and_ringKrullDim_succ_eq`: for `x ∈ 𝔪 \ 𝔪²` in a regular local
  ring `R`, `R ⧸ (x)` is regular and `dim (R ⧸ (x)) + 1 = dim R`; the two halves are
  `isRegularLocalRing_quotient_span_singleton` and `ringKrullDim_quotient_span_singleton_succ_eq`,
  and `spanFinrank_maximalIdeal_quotient_succ_eq` counts generators.
- `#guard_msgs` checks record that the results use only the standard axioms.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `RegularQuotientEngine.isLocalRing_quotient_span_singleton`
- theorem `RegularQuotientEngine.exists_span_eq_maximalIdeal_ncard_le`
- theorem `RegularQuotientEngine.one_le_spanFinrank_maximalIdeal_of_notMem_sq`
- theorem `RegularQuotientEngine.spanFinrank_map_quotientMk_le_sub_one`
- theorem `RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_le_sub_one`
- theorem `RegularQuotientEngine.ringKrullDim_lt_top_of_isNoetherianRing_of_isLocalRing`
- theorem `RegularQuotientEngine.exists_ringKrullDim_eq_natCast`
- theorem `RegularQuotientEngine.isRegularLocalRing_quotient_and_ringKrullDim_succ_eq`
- theorem `RegularQuotientEngine.isRegularLocalRing_quotient_span_singleton`
- theorem `RegularQuotientEngine.ringKrullDim_quotient_span_singleton_succ_eq`
- theorem `RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_succ_eq`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
