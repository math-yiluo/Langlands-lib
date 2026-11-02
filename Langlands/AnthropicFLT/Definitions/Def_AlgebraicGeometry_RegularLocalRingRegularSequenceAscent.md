# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RegularLocalRingRegularSequenceAscent`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_RegularLocalRingRegularSequenceAscent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Regular local rings: ascent along a quotient by a regular sequence (namespace
`RegularLocalRingQuotientAscent`).

- Section `Preliminaries`: elements of a regular sequence lie in the maximal ideal and are
  non-zero-divisors; the ideal `Ideal.ofList rs` of a regular sequence is proper and has at most
  `rs.length` generators.
- Section `Ascent`: if `rs` is a regular sequence in a noetherian local ring `A` and
  `A ⧸ Ideal.ofList rs` is a regular local ring, then `A` is regular
  (`isRegularLocalRing_of_isRegularLocalRing_quotient_ofList`, with variants for weakly regular
  sequences in the maximal ideal and for surjections whose kernel is `Ideal.ofList rs`). The key
  estimate is `spanFinrank_maximalIdeal_le_quotient_ofList_add_length`.
- Section `IteratedAscent`: the same result proved by induction on the length, using the
  one-element ascent of `Def_AlgebraicGeometry_RegularLocalRingQuotientNonZeroDivisorAscent`.
- Sections `Gates` and `Teeth`: `ℤ_[p]` with the regular sequence `[p]` satisfies the hypotheses;
  without regularity of the sequence the conclusion fails (dual numbers).
- `#guard_msgs` checks record that the main results use only the standard axioms.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `RegularLocalRingQuotientAscent.mem_nonZeroDivisors_of_isSMulRegular`
- theorem `RegularLocalRingQuotientAscent.ofList_ne_top_of_isRegular`
- theorem `RegularLocalRingQuotientAscent.mem_maximalIdeal_of_isRegular`
- theorem `RegularLocalRingQuotientAscent.spanFinrank_ofList_le_length`
- theorem `RegularLocalRingQuotientAscent.spanFinrank_maximalIdeal_le_quotient_ofList_add_length`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient_ofList`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient_isWeaklyRegular`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient_regularSequence`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_surjective_ker_ofList`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient_ofList_iterated`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient_ofList_via_iterated_ascent`
- theorem `RegularLocalRingQuotientAscent.gate_padicInt_isRegular_singleton_p`
- theorem `RegularLocalRingQuotientAscent.gate_padicInt_quotient_ofList_isRegularLocalRing`
- theorem `RegularLocalRingQuotientAscent.gate_isRegularLocalRing_padicInt_via_sequence`
- theorem `RegularLocalRingQuotientAscent.gate_isRegularLocalRing_padicInt_via_iterated_ascent`
- theorem `RegularLocalRingQuotientAscent.gate_padicInt_dimension_jump_length`
- theorem `RegularLocalRingQuotientAscent.not_isRegular_dualNumber_singleton_eps`
- theorem `RegularLocalRingQuotientAscent.not_forall_isRegularLocalRing_of_quotient_ofList_dropping_isRegular`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RegularLocalRingQuotientNonZeroDivisorAscent` (same contribution).
Other imports: `Mathlib`.
