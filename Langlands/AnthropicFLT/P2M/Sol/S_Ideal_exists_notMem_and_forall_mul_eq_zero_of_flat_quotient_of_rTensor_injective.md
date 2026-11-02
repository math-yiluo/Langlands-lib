# `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective`. Statement. `Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective`: let `J ⊆ A` be a finitely generated
ideal of an `R`-algebra with `A/J` flat over `R`, `𝔭 ⊆ A` prime, and `K` a field over `R` whose kernel is the
contraction of `𝔭`. If `A ⊗_R K → (A/J) ⊗_R K` is injective, then some `s ∉ 𝔭` kills `J`.

Proof. Since `A/J` is flat, tensoring `0 → J → A → A/J → 0` with `K` stays exact (ported
`Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat`); with the injectivity hypothesis, `J ⊗_R K = 0`. As
`J` is finitely generated, Nakayama's lemma over the localization at `𝔭` (the fibre `K` sees `J_𝔭 / 𝔭 J_𝔭`) gives
`J_𝔭 = 0`, i.e. some `s ∉ 𝔭` kills the finitely many generators (local `exists_ne_zero_and_smul_eq_zero`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.K63A2a.exists_ne_zero_and_smul_eq_zero`
- theorem `P2MW.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat` (Library).
Other imports: `Mathlib`.
