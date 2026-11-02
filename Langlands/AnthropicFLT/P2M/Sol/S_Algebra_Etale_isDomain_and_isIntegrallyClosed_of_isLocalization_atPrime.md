# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `EtaleLocNormalAux`). Let `L` be the fraction field of `P`. Section `Core`: `A`
embeds in its generic fibre `A ⊗[P] L` (flatness, `algebraMap_genericFibre_injective`) and is
integrally closed in it (`smooth_integrallyClosed_in_genericFibre`, from Mathlib's
`TensorProduct.toIntegralClosure_bijective_of_smooth` and integral closedness of `P`). The generic
fibre is étale over the field `L`, hence a finite product `∏ F_j` of fields
(`Algebra.FormallyEtale.iff_exists_algEquiv_prod`). Its idempotents are integral
(`isIntegral_of_isIdempotentElem`), hence come from `A`; they sum to `1`, so one of them, `ε i`, is
not in `q`. The projection `ρ : A → F i` extends to an injective map `A_q → F i`, so `A_q` is a
domain; an element of `F i` integral over `A_q` comes from `A_q` (clear denominators and use the
integral closedness of `A` in the generic fibre), so `A_q` is integrally closed
(`isIntegrallyClosed_of_integralClosure_eq_bot`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.EtaleLocNormalAux.isIntegral_of_isIdempotentElem`
- theorem `P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.EtaleLocNormalAux.tensorMap_integralClosure_mem_bot`
- theorem `P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.EtaleLocNormalAux.smooth_integrallyClosed_in_genericFibre`
- theorem `P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.EtaleLocNormalAux.exists_algebraMap_eq_of_isIntegral_genericFibre`
- theorem `P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.EtaleLocNormalAux.algebraMap_genericFibre_injective`
- theorem `P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.EtaleLocNormalAux.isIntegrallyClosed_of_integralClosure_eq_bot`
- theorem `P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
