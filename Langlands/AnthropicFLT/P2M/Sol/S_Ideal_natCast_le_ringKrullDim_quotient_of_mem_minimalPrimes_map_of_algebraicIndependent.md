# `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 91, line 102 here): the FLT text
  `rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,       Nat.card_eq_fintype_card, Fintype.card_fin]   rw [h2] at h1`
  is replaced by
  `rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,       ENat.card_eq_coe_fintype_card, Fintype.card_fin]     rfl   rw [h2] at h1`.
  In the project's Mathlib, `MvPolynomial.ringKrullDim_of_isNoetherianRing` expresses the number of variables as `ENat.card σ` instead of `Nat.card σ`, so `Nat.card_eq_fintype_card` is replaced by `ENat.card_eq_coe_fintype_card` (Mathlib `SetTheory/Cardinal/Finite.lean`); the remaining goal, which differs only by the coercion through `ℕ∞`, is closed by `rfl`.
- Manual edit for Mathlib drift (FLT line 252, line 264 here): the FLT text
  `rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]   calc`
  is replaced by
  `rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ENat.card_eq_coe_fintype_card, Fintype.card_fin]     rfl   calc`.
  In the project's Mathlib, `MvPolynomial.ringKrullDim_of_isNoetherianRing` expresses the number of variables as `ENat.card σ` instead of `Nat.card σ`, so `Nat.card_eq_fintype_card` is replaced by `ENat.card_eq_coe_fintype_card` (Mathlib `SetTheory/Cardinal/Finite.lean`); the remaining goal, which differs only by the coercion through `ℕ∞`, is closed by `rfl`.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent`. Statement. `Ideal.natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent`: let `R ⊆ C` be finitely
generated domains over `k`, `z₁, …, z_d ∈ C` algebraically independent over `R` such that, after inverting `r ≠ 0`,
`C` is integral over `R[z]`. For a maximal `p ⊆ R` with `r ∉ p` and a minimal prime `Q` over `pC`,
`d ≤ dim C/Q`.

Proof. Localize at `r`: `C_r` is integral over `R_r[z]`, so `C_r / Q` is integral over its image, a quotient of
`(R/p)[z]`. Minimality of `Q` and the dimension formula (ported
`Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType`) show that `Q` contracts to `p[z]`, so
`C/Q` is integral over a polynomial ring in `d` variables over the field `R/p` and has dimension `≥ d`
(`ringKrullDim_le_of_isIntegral_of_injective`, `ringKrullDim_localization_le`, `ringKrullDim_localization_add_le`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private lemma `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.P2mFibDim.exists_ltSeries_comap_eq_last`
- theorem `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.P2mFibDim.ringKrullDim_le_of_isIntegral_of_injective`
- theorem `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.P2mFibDim.ringKrullDim_localization_le`
- lemma `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.P2mFibDim.exists_nat_eq`
- theorem `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.P2mFibDim.exists_ringKrullDim_eq_natCast`
- theorem `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.P2mFibDim.ringKrullDim_localization_add_le`
- theorem `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.P2mFibDim.main`
- theorem `P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType` (same contribution).
Other imports: `Mathlib`.
