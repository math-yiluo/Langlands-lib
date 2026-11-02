# `Langlands.AnthropicFLT.P2M.Sol.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le`. Statement. `fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le`: over a field of characteristic zero, a function
`f : ℤ → R` has vanishing `(d + 1)`-st forward difference iff it is given by a polynomial of degree `≤ d`.

Proof. Backward direction: forward differences lower the degree of a polynomial by one (`iter_eq_zero_of_polynomial`).
Forward direction: Newton interpolation; the polynomial `Σ_{k ≤ d} Δᵏ f(0) · C(X, k)` (`binom`, `newton`,
`natDegree_newton_le`) has the same forward differences at `0`, and a function whose `(d + 1)`-st difference vanishes is
determined by these values (`eq_newton_eval`, `exists_polynomial`, `main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.binom`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.binom_eval_natCast`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.natDegree_binom_le`
- def `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.newton`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.natDegree_newton_le`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.newton_eval`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.iter_zero`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.iter_eq_zero_of_le`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.eq_newton_eval`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.newton_eq_newton`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.exists_polynomial`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.iter_eq_zero_of_polynomial`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.P2mNewton.main`
- theorem `P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
