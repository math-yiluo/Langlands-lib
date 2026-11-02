# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 8 lines the replacements `Type` (universe 0) → `Type uz` (8 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval`. Statement. `MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval`: let `P` be the Hilbert polynomial of some
homogeneous ideal over some field. There is `D₀` such that for every `e ≥ D₀`: every ideal `J` generated in degree `e`
with `h_J(e) = P(e)` has `h_J(e + 1) ≤ P(e + 1)`, and some ideal generated in degree `e` has `h_J(e) = P(e)` and
`h_J(e + 1) = P(e + 1)`.

Proof. By the ported `Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow`, for large `e` the values of `P` satisfy
`P(e + 1) = P(e)^⟨e⟩` (Macaulay representations of Hilbert polynomials stabilize; the bound `P(e) ≤ dim of forms` comes
from `finrank_piece_le`, `finrank_homogeneousSubmodule`). The inequality is then Macaulay's bound (ported
`MvPolynomial.finrank_piece_succ_le_macaulayPow`), and equality is attained by the lex-segment ideal of the ported
`MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.GotzNumber.finite_homogeneousSubmodule`
- theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.GotzNumber.natCard_degree_eq`
- theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.GotzNumber.finrank_homogeneousSubmodule`
- theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.GotzNumber.finrank_piece_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.GotzNumber.decompose_eq`
- theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.GotzNumber.span_homogeneous`
- theorem `P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow` (same contribution).
Other imports: `Mathlib`.
