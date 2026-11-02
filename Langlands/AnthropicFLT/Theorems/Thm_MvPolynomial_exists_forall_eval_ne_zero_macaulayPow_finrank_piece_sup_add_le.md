# `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.solution n d hd K J hJ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 18 here); in 1 line the replacements `Type` (universe 0) → `Type uz` (1 place) are made, and these lines are otherwise unchanged. Consequently the theorem statement becomes universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le` (a hyperplane restriction inequality):
let `J` be a homogeneous ideal of `K[x₀, …, x_n]` over an infinite field and `d ≥ 1`; write `h_I(d)` for the dimension
of the degree-`d` part of `K[x]/I` and `a^⟨d⟩` for `Nat.macaulayPow d a`. There is a nonzero polynomial `G` such that
for every linear form `ℓ = Σ aᵢ xᵢ` with `G(a) ≠ 0`, `h_{J+(ℓ)}(d)^⟨d⟩ + h_J(d) ≤ h_J(d)^⟨d⟩`.

The proof term applies the companion solution theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le` (same contribution).
Other imports: `Mathlib`.
