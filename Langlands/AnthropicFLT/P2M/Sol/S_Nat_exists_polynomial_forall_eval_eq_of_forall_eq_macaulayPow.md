# `Langlands.AnthropicFLT.P2M.Sol.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow`. Statement. `Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow`: if `H(e + 1) = H(e)^⟨e⟩` for all `e ≥ D₀ ≥ 1`, then `H`
agrees with a rational polynomial for `e ≥ D₀`.

Proof. Iterating the Macaulay power shifts every binomial coefficient `C(a_i, i)` of the representation of `H(D₀)` to
`C(a_i + (e - D₀), i + (e - D₀))` (`G`, `G_succ`, `G_eq`, `top_G`, `rem_G`); each such term is a polynomial in `e`
(`exists_poly_choose`, `exists_poly_tail_zero`, `exists_poly_G`), and so is their finite sum.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top`
- def `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.rem`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.macaulayPow_zero`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.macaulayPow_succ`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.sub_le_choose`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.choose_top_le`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_le`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.lt_choose_of_top_lt`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.lt_choose_top_succ`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_eq_of`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.le_top_of_choose_le`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_lt_of_lt_choose`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.d_le_top`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_zero_right`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.d_lt_top_of_pos`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_zero_left`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.rem_zero_left`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.rem_add_choose`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.rem_lt`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_mono`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.macaulayPow_lt_choose`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_macaulayPow`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.rem_macaulayPow`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.macaulayPow_zero_right`
- def `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.G`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.G_zero`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.G_succ`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.G_zero_mid`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.top_G`
- def `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.tail`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.rem_G`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.G_eq`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.exists_poly_choose`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.exists_poly_tail_zero`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.PolyMaxSol.exists_poly_G`
- theorem `P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution).
Other imports: `Mathlib`.
