# `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.solution n g hg H hH K J hJ hev`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 1 line the replacements `Type` (universe 0) → `Type uz` (1 place) are made, and these lines are otherwise unchanged. Consequently the theorem statement becomes universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq`: let `H` satisfy
`H(e + 1) = H(e)^⟨e⟩` for `e ≥ g ≥ 1`. If the Hilbert function of a homogeneous ideal `J` agrees with `H` eventually, then
`H(d) ≤ h_J(d)` for all `d ≥ g`.

The proof term applies the companion solution theorem `P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq` (same contribution).
Other imports: `Mathlib`.
