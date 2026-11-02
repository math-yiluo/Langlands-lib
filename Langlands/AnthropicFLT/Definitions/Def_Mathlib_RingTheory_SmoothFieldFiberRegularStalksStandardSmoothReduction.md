# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Reduction of `SmoothFieldFiberRegularStalksInput` to standard smooth algebras (theorems prefixed
`kmf2_fiber_`).

- `kmf2_fiber_input_of_standardSmooth_case`, `kmf2_fiber_standardSmooth_case_of_input`,
  `kmf2_fiber_input_iff_standardSmooth_case`: the input proposition holds iff every standard smooth
  algebra over a field has regular localizations at primes (smooth algebras are locally standard
  smooth).
- Checks: localizations of principal ideal domains, of `k[X]`, and of a reduced noetherian ring at
  a minimal prime are regular; `k[X]` is smooth over `k`; the dual numbers show that the
  smoothness hypotheses cannot be dropped.
- `#guard_msgs` checks record that the results use only the standard axioms.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `kmf2_fiber_isLocalization_primeCompl_congr`
- theorem `kmf2_fiber_input_of_standardSmooth_case`
- theorem `kmf2_fiber_standardSmooth_case_of_input`
- theorem `kmf2_fiber_input_iff_standardSmooth_case`
- theorem `kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isPrincipalIdealRing`
- theorem `kmf2_fiber_isRegularRing_polynomial`
- theorem `kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial`
- theorem `kmf2_fiber_sat_smooth_polynomial`
- theorem `kmf2_fiber_gate_input_clause_polynomial`
- theorem `kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isReduced_of_mem_minimalPrimes`
- theorem `kmf2_fiber_falsif_not_standardSmooth_case_dropping_standardSmooth`
- theorem `kmf2_fiber_not_isStandardSmooth_dualNumber_of_standardSmooth_case`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks` (same contribution).
Other imports: `Mathlib`.
