# `Langlands.AnthropicFLT.P2M.Sol.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 99, line 110 here): `((IsDiscreteValuationRing.TFAE B hnf).out 0 4)` is replaced by `((IsDiscreteValuationRing.TFAE B hnf).out 1 5)`. In the project's Mathlib, `List.TFAE.out` takes 1-indexed positions (FLT's Mathlib used 0-indexed ones); the list of `IsDiscreteValuationRing.TFAE` is unchanged, so both indices are increased by one and the proved equivalence is the same.
- No other change: the declarations and statements are the FLT ones, and the proofs are the FLT text except for the edits above.

## Content

Proof (namespace `Ws10Flat.Local`). If `𝔪` is associated to `B ⧸ (x)`, then `𝔪 = (x) : y` for some
`y` (`exists_maximalIdeal_eq_colon_of_eq_radical_colon`, `colon_bot_quotient_mk_eq`). Consider
`z = y / x` in the fraction field: either `z 𝔪 ⊆ 𝔪`, so `z` is integral and lies in `B`, which
contradicts `y ∉ (x)`; or `z 𝔪 = B`, so `𝔪 = (x / y)` is principal and nonzero, and `B` is a
discrete valuation ring (`IsDiscreteValuationRing.TFAE`). The chain of lemmas is
`isDiscreteValuationRing_of_maximalIdeal_eq_colon`,
`isDiscreteValuationRing_of_maximalIdeal_eq_radical_colon`,
`isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.Ws10Flat.exists_maximalIdeal_eq_colon_of_eq_radical_colon`
- theorem `P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.Ws10Flat.colon_bot_quotient_mk_eq`
- theorem `P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.Ws10Flat.isDiscreteValuationRing_of_maximalIdeal_eq_colon`
- theorem `P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.Ws10Flat.isDiscreteValuationRing_of_maximalIdeal_eq_radical_colon`
- theorem `P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.Ws10Flat.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes`
- theorem `P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
