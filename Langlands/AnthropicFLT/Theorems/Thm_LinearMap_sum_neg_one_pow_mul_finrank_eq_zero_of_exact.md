# `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.solution A B C f g δ hf0 hfg hgδ hδf N hN`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact`: for a long exact sequence
`0 → A₀ → B₀ → C₀ → A₁ → ⋯` of finite-dimensional vector spaces with `A_N = 0`, the alternating sum
`Σ_{i<N} (-1)^i (dim Aᵢ - dim Bᵢ + dim Cᵢ)` vanishes.

The proof term applies the companion solution theorem `P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact` (same contribution).
Other imports: `Mathlib`.
