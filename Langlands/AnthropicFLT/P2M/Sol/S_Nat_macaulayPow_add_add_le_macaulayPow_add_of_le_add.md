# `Langlands.AnthropicFLT.P2M.Sol.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add`. Statement. `Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add`: for `d ≥ 1` and `x ≤ u + v`, if `u^⟨d⟩ + y ≤ y^⟨d⟩` and
`v^⟨d+1⟩ + x ≤ x^⟨d+1⟩`, then `x^⟨d+1⟩ + (x + y) ≤ (x + y)^⟨d+1⟩` (an arithmetic inequality used in the hyperplane
restriction argument).

Proof. Manipulation of Macaulay representations: the "lower" Macaulay function `low` (an inverse of `macaulayPow`,
`low_lt_choose`, `macaulayPow_low_add`, `le_choose_add_low`, `le_add_low`) converts the hypotheses into bounds on `x`
and `y` relative to their representations, and strict monotonicity of `macaulayPow` (`macaulayPow_strictMono`,
`le_of_macaulayPow_le`, `le_macaulayPow_sub_low`) gives the conclusion; the case analysis follows the leading binomial
coefficient (`top`, `rem`, `top_succ_of_le`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.top`
- def `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.rem`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_zero`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_succ`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.sub_le_choose`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.choose_top_le`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.lt_choose_of_top_lt`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.lt_choose_top_succ`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.top_eq_of`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.le_top_of_choose_le`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.top_lt_of_lt_choose`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.d_le_top`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.top_zero_right`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.d_lt_top_of_pos`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.top_zero_left`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.rem_zero_left`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.rem_zero_right`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.rem_add_choose`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.rem_lt`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_lt_choose`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_mono`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_one`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_zero_right`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.top_succ_of_le`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_eq_self`
- def `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.low`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.low_zero`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.low_succ`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.low_zero_right`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.low_eq_zero`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.low_lt_choose`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_low_add`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.le_choose_add_low`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.le_add_low`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.low_le`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_lt_succ`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.macaulayPow_strictMono`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.le_of_macaulayPow_le`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.GreenNum.le_macaulayPow_sub_low`
- theorem `P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution).
Other imports: `Mathlib`.
