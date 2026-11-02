# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RegularLocalRingQuotientNonZeroDivisorAscent`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_RegularLocalRingQuotientNonZeroDivisorAscent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Regular local rings: ascent along a quotient by one non-zero-divisor (namespace
`RegularLocalRingQuotientAscent`).

- Section `GeneratorCounting`: a surjection of local rings does not increase the minimal number of
  generators of the maximal ideal (`spanFinrank_comap_le_of_surjective`,
  `spanFinrank_maximalIdeal_le_of_surjective`) or the dimension of the cotangent space
  (`finrank_cotangentSpace_le_of_surjective`).
- Section `Ascent`: `isRegularLocalRing_of_isRegularLocalRing_quotient`: if `x` is a non-zero-divisor
  in the maximal ideal of a noetherian local ring `A` and `A ⧸ (x)` is regular, then `A` is regular;
  `isRegularLocalRing_of_surjective_ker_span_singleton` is the same for a surjection with kernel
  `(x)`.
- Section `Gates` (sanity checks): the ring of `p`-adic integers `ℤ_[p]` with `ℤ_[p] ⧸ (p) ≅ ZMod p`
  (`padicIntQuotientSpanPEquiv`) satisfies the hypotheses, and is regular.
- Section `Teeth` (necessity of the non-zero-divisor hypothesis): the dual numbers `K[ε]` are not
  regular although `K[ε] ⧸ (ε) ≅ K` is (`not_isRegularLocalRing_dualNumber`,
  `not_forall_isRegularLocalRing_of_quotient_dropping_nonZeroDivisor`).
- `#guard_msgs` checks record that the main results use only the standard axioms.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `RegularLocalRingQuotientAscent.spanFinrank_comap_le_of_surjective`
- theorem `RegularLocalRingQuotientAscent.spanFinrank_maximalIdeal_le_of_surjective`
- theorem `RegularLocalRingQuotientAscent.finrank_cotangentSpace_le_of_surjective`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient`
- theorem `RegularLocalRingQuotientAscent.isRegularLocalRing_of_surjective_ker_span_singleton`
- def `RegularLocalRingQuotientAscent.padicIntQuotientSpanPEquiv`
- theorem `RegularLocalRingQuotientAscent.gate_padicInt_hypotheses`
- theorem `RegularLocalRingQuotientAscent.gate_isRegularLocalRing_padicInt`
- theorem `RegularLocalRingQuotientAscent.gate_padicInt_conclusion_consistency`
- theorem `RegularLocalRingQuotientAscent.gate_padicInt_dimension_jump`
- def `RegularLocalRingQuotientAscent.dualNumberFst`
- theorem `RegularLocalRingQuotientAscent.dualNumberFst_apply`
- theorem `RegularLocalRingQuotientAscent.ker_dualNumberFst`
- theorem `RegularLocalRingQuotientAscent.dualNumberFst_surjective`
- def `RegularLocalRingQuotientAscent.dualNumberQuotientSpanEpsEquiv`
- theorem `RegularLocalRingQuotientAscent.quotient_span_eps_isRegularLocalRing`
- theorem `RegularLocalRingQuotientAscent.eps_ne_zero`
- theorem `RegularLocalRingQuotientAscent.eps_notMem_nonZeroDivisors`
- theorem `RegularLocalRingQuotientAscent.eps_mem_maximalIdeal`
- theorem `RegularLocalRingQuotientAscent.not_isRegularLocalRing_dualNumber`
- theorem `RegularLocalRingQuotientAscent.not_forall_isRegularLocalRing_of_quotient_dropping_nonZeroDivisor`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
