# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact`. Statement. `LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact`: for a long exact sequence
`0 → A₀ → B₀ → C₀ → A₁ → ⋯` of finite-dimensional vector spaces with `A_N = 0`, the alternating sum
`Σ_{i<N} (-1)^i (dim Aᵢ - dim Bᵢ + dim Cᵢ)` vanishes.

Proof. Write each dimension as the rank of the outgoing map plus the dimension of its kernel (local
`finrank_eq_range_add_ker`); by exactness consecutive terms cancel and the sum telescopes (`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.P2mLES.finrank_eq_range_add_ker`
- theorem `P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.P2mLES.main`
- theorem `P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
