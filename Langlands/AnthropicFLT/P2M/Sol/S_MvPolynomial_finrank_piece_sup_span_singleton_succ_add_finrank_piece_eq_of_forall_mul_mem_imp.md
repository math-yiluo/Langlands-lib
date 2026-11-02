# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 17 here); in 2 lines the replacements `Type` (universe 0) → `Type uz` (2 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp`. Statement. `MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp`: if the linear form
`ℓ` is a nonzerodivisor modulo the homogeneous ideal `J` on all forms, then `h_{J+(ℓ)}(d + 1) + h_J(d) = h_J(d + 1)`.

Proof. The sequence `0 → (K[x]/J)_d --ℓ--> (K[x]/J)_{d+1} → (K[x]/(J + ℓ))_{d+1} → 0` is exact: injectivity is the
nonzerodivisor hypothesis and exactness in the middle is the description of the degree-`(d + 1)` part of `J + (ℓ)`
(`Jd`, `mulLin`, `homogeneousComponent_mul_linear`); count dimensions.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.P2mWs6HP.Jd`
- theorem `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.P2mWs6HP.mem_Jd`
- scoped instance `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.P2mWs6HP.finite_homogeneousSubmodule`
- def `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.P2mWs6HP.mulLin`
- theorem `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.P2mWs6HP.mulLin_apply`
- theorem `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.P2mWs6HP.homogeneousComponent_mul_linear`
- theorem `P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution).
Other imports: `Mathlib`.
