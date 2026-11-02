# `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 87, line 98 here): `Nat.card_eq_fintype_card, Fintype.card_fin]` is replaced by `ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  rfl`. In the project's Mathlib, `MvPolynomial.ringKrullDim_of_isNoetherianRing` expresses the number of variables as `ENat.card σ` instead of `Nat.card σ`, so `Nat.card_eq_fintype_card` is replaced by `ENat.card_eq_coe_fintype_card` (Mathlib `SetTheory/Cardinal/Finite.lean`). After these rewrites the goal `((s : ℕ∞) : WithBot ℕ∞) = (s : WithBot ℕ∞)` remains (the coercion now passes through `ℕ∞`); it holds by `rfl`.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType`. Statement. `Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType` (dimension formula): for a finitely generated
domain `A` over a field and a prime `P`, `ht P + dim A/P = dim A`.

Proof. By Noether normalization `A` is integral over a polynomial ring `k[x₁, …, x_n]`, with `dim A = n`
(`ringKrullDim_eq_of_isIntegral_of_injective`, `ringKrullDim_mvPolynomial_fin`). Heights are preserved under the
integral extension by going down for integrally closed bases (`height_eq_height_under_of_hasGoingDown`) and maximal
ideals of the polynomial ring have height `n` (`height_eq_of_isMaximal_mvPolynomial`,
`height_eq_ringKrullDim_of_isMaximal`). The inequality `ht P + dim A/P ≤ dim A` is formal
(`height_add_ringKrullDim_quotient_le`); the reverse is proved by induction on `ht P`, cutting down by one element at a
time (`ringKrullDim_quotient_radical_span_add_one`, `ringKrullDim_quotient_add_one_of_height_eq_one`,
`height_head_add_length_le`) and using that chains of primes can be refined.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private lemma `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.exists_ltSeries_comap_eq_last`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_eq_of_isIntegral_of_injective`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.height_le_height_under_of_isIntegral`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.height_eq_height_under_of_hasGoingDown`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_mvPolynomial_fin`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.height_eq_of_isMaximal_mvPolynomial`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.height_eq_ringKrullDim_of_isMaximal`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_quotient_radical`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_quotient_radical_span_add_one`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.exists_ringKrullDim_eq_natCast`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.height_head_add_length_le`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.height_map_mk_add_height_le`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_quotient_eq_coheight`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.height_add_ringKrullDim_quotient_le`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_quotient_add_one_of_height_eq_one`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.main`
- theorem `P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
