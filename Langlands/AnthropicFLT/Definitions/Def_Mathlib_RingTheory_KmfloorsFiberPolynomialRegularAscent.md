# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Regularity of polynomial rings over regular rings (theorems prefixed `kmf2_polyasc_`).

- Transport lemmas for localizations at equal primes, and regularity of localizations given by
  `IsLocalization` at a prime complement.
- For a domain `D` and a prime `Q` of `D[X]` meeting `D` only in `0`, the localization `D[X]_Q` is
  regular (`..._localization_atPrime_of_comap_C_eq_bot`).
- For a prime `P` of `R[X]` over `p = P ∩ R`, regularity of the fibre ring
  (`..._localization_atPrime_fiberPrime`, `..._quotient_fiber`).
- `kmf2_polyasc_isRegularLocalRing_localization_atPrime_polynomial_of_isRegularRing` and
  `kmf2_polyasc_isRegularRing_polynomial_of_isRegularRing`: if `R` is a regular ring, so is
  `R[X]`; hence `MvPolynomial (Fin n) k` is regular for a field `k`
  (`kmf2_polyasc_isRegularRing_mvPolynomial_fin`, by induction on `n`).
- Gates: polynomial rings over a field are smooth with regular localizations, and `ℤ[X]` is
  regular.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `kmf2_polyasc_isLocalization_primeCompl_congr`
- theorem `kmf2_polyasc_isRegularLocalRing_of_isLocalization_primeCompl`
- theorem `kmf2_polyasc_isRegularLocalRing_atPrime_of_isLocalization_primeCompl`
- theorem `kmf2_polyasc_isRegularLocalRing_localization_atPrime_of_comap_C_eq_bot`
- theorem `kmf2_polyasc_isRegularLocalRing_localization_atPrime_fiberPrime`
- theorem `kmf2_polyasc_isRegularLocalRing_quotient_fiber`
- theorem `kmf2_polyasc_isRegularLocalRing_localization_atPrime_polynomial_of_isRegularRing`
- theorem `kmf2_polyasc_isRegularRing_polynomial_of_isRegularRing`
- theorem `kmf2_polyasc_isRegularRing_mvPolynomial_fin`
- theorem `kmf2_polyasc_gate_input_clause_mvPolynomial`
- theorem `kmf2_polyasc_gate_isRegularRing_polynomial_int`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscent` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction` (same contribution).
Other imports: `Mathlib`.
