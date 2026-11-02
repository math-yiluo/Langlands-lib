# `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 64, line 75 here): the FLT text
  `Nat.card_eq_fintype_card, Fintype.card_fin]  theorem height_eq_of_isMaximal_mvPolynomial`
  is replaced by
  `ENat.card_eq_coe_fintype_card, Fintype.card_fin]   rfl  theorem height_eq_of_isMaximal_mvPolynomial`.
  In the project's Mathlib, `MvPolynomial.ringKrullDim_of_isNoetherianRing` expresses the number of variables as `ENat.card σ` instead of `Nat.card σ`, so `Nat.card_eq_fintype_card` is replaced by `ENat.card_eq_coe_fintype_card` (Mathlib `SetTheory/Cardinal/Finite.lean`); the remaining goal, which differs only by the coercion through `ℕ∞`, is closed by `rfl`.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one`. Statement. `Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one`: let `A` be a finitely generated domain over an
algebraically closed field `k` with `dim A ≥ 1`, and `m₀`, `m₁` maximal ideals. There is a prime `P ⊆ m₀ ∩ m₁` with
`dim A/P = 1` (a curve through both points).

Proof. Induction on `dim A` (`main`, `step`). If `dim A = 1`, take `P = 0`. If `dim A ≥ 2`, arrange `m₀ ≠ m₁`
(local `exists_isMaximal_ne` when they coincide) and use the ported `Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime`
to get `f ≠ 0` in `m₀ ∩ m₁` with `√(f)` prime; then `dim A/√(f) = dim A - 1` (local
`ringKrullDim_quotient_radical_span_add_one`, from the principal ideal theorem and the dimension formula for
finitely generated domains, `height_eq_ringKrullDim_of_isMaximal`, via Noether normalization), and the induction
hypothesis in `A/√(f)` gives a prime whose preimage in `A` works (`comap_mk_le`, `ringKrullDim_quotient_comap_mk`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private lemma `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.exists_ltSeries_comap_eq_last`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.ringKrullDim_eq_of_isIntegral_of_injective`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.ringKrullDim_mvPolynomial_fin`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.height_eq_of_isMaximal_mvPolynomial`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.height_eq_ringKrullDim_of_isMaximal`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.ringKrullDim_quotient_radical`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.ringKrullDim_quotient_radical_span_add_one`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.exists_ringKrullDim_eq_natCast`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.exists_isMaximal_ne`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.step`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.comap_mk_le`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.ringKrullDim_quotient_comap_mk`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.main`
- theorem `P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime` (same contribution).
Other imports: `Mathlib`.
