# `Langlands.AnthropicFLT.Theorems.Thm_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced`

Ported for task `c23cb2c8-d7bd-4f3b-904d-448ce5a3c826` (proof of `Langlands.GroupScheme.AffineHomImageStatement`), as part of the FLT closure of `HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem`. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.solution p K hΔ hS hfg`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced p K hΔ hS hfg`: let `k` be a perfect field of
characteristic `p` (with `p` prime) and `H` a commutative Hopf algebra over `k` (in universes `u` and `v`). Let `K`
be a finitely generated `k`-subalgebra of `H` (`hfg`) such that `Δ x` lies in the `k`-span of
`{a ⊗ b | a ∈ K, b ∈ K}` for every `x ∈ K` (`hΔ`) and `K` is stable under the antipode (`hS`). Then there are `r : ℕ`
and a `k`-subalgebra `K' ≤ K` such that

- `K'` is finitely generated and reduced (`IsReduced ↥K'`);
- the underlying set of `K'` is exactly `{x ^ p ^ r | x ∈ K}`;
- `K'` satisfies the same comultiplication condition and is stable under the antipode.

Geometrically: the `r`-th relative Frobenius maps the (possibly nonreduced) group `Spec K` onto a reduced group
`Spec K'`. Compare J. S. Milne, *Algebraic Groups* (Cambridge University Press 2017; project copy: the 2022
corrected reprint), Proposition 3.29, used in the proof of Theorem 3.31: for some `n`, `O(H) ^ p ^ n` is a reduced
Hopf subalgebra of `O(H)`.

The proof term applies the companion solution theorem `P2MW.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced` (same contribution).
Other imports: `Mathlib`.
