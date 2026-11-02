# `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `W2RLR`, development `No4PatchingCore`). Section `DimensionDrop`:
`ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes` rewrites both dimensions as
support dimensions and applies Mathlib's
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal`;
`ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes` transfers this from
`QuotSMulTop x R` to `R ⧸ (x)`, and `solution` applies it. The file also contains the sections
`FromABFreeness`, `Exchange0`, `PrimeAvoidance`, `QuotientRegularity` and `MatsumuraDomain`
(regular local rings are domains), shared with the proof of `IsRegularLocalRing.isDomain`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.maximalIdeal_ne_bot_of_ringKrullDim_pos`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.isLocalRing_quotient_span_singleton`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.exists_ringKrullDim_eq_natCast`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.exists_finite_span_eq_maximalIdeal_mem`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.exists_parameter_notMem_minimalPrimes`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.annihilator_self_eq_bot`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.isDomain_of_isRegularLocalRing_aux`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.W2RLR.No4PatchingCore.isDomain_of_isRegularLocalRing`
- theorem `P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
