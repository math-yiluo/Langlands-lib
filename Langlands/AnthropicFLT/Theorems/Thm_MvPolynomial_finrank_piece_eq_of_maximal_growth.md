# `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_eq_of_maximal_growth`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_MvPolynomial_finrank_piece_eq_of_maximal_growth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finrank_piece_eq_of_maximal_growth.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_MvPolynomial_finrank_piece_eq_of_maximal_growth.solution n m h h₂ h₃ K J hJ hm hm₁`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 17 here); in 3 lines the replacements `Type` (universe 0) → `Type uz` (3 places) are made, and these lines are otherwise unchanged. Consequently the theorem statement becomes universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `MvPolynomial.finrank_piece_eq_of_maximal_growth` (Gotzmann persistence for a numerical function): let `h : ℕ → ℕ`
satisfy, for `e ≥ m`, the bound "every ideal generated in degree `e` with `h_J(e) = h(e)` has `h_J(e + 1) ≤ h(e + 1)`"
and the realizability "some ideal generated in degree `e` has `h_J(e) = h(e)` and `h_J(e + 1) = h(e + 1)`". If `J` is
generated in degree `m` with `h_J(m) = h(m)` and `h_J(m + 1) = h(m + 1)`, then `h_J(e) = h(e)` for all `e ≥ m`.

The proof term applies the companion solution theorem `P2MW.S_MvPolynomial_finrank_piece_eq_of_maximal_growth.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `MvPolynomial.finrank_piece_eq_of_maximal_growth`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_finrank_piece_eq_of_maximal_growth` (same contribution).
Other imports: `Mathlib`.
