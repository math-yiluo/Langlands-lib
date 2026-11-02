# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_finrank_piece_succ_le_macaulayPow`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_finrank_piece_succ_le_macaulayPow.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 187, line 199 here): `{ toFun := fun p a => coeff a.1 (p.1 : MvPolynomial (Fin (n + 1)) K)` is replaced by `{ toFun := fun p a => (p.1 : MvPolynomial (Fin (n + 1)) K).coeff a.1`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 200, line 212 here): `change coeff ((lex n).degree (p.1 : MvPolynomial (Fin (n + 1)) K)) (p.1 : MvPolynomial (Fin (n + 1)) K) = 0 at this` is replaced by `change (p.1 : MvPolynomial (Fin (n + 1)) K).coeff ((lex n).degree (p.1 : MvPolynomial (Fin (n + 1)) K)) = 0 at this`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 224, line 236 here): `have hcoeff : coeff a₀.1 (∑ a, c a • g a) = c a₀ * (lex n).leadingCoeff (g a₀) := by` is replaced by `have hcoeff : (∑ a, c a • g a).coeff a₀.1 = c a₀ * (lex n).leadingCoeff (g a₀) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 236, line 248 here): `rw [hc, coeff_zero] at hcoeff` is replaced by `rw [hc, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 17 here); in 2 lines the replacements `Type` (universe 0) → `Type uz` (2 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow`. Statement. `MvPolynomial.finrank_piece_succ_le_macaulayPow` (Macaulay's theorem): for a homogeneous ideal `J` of
`K[x₀, …, x_n]` and `d ≥ 1`, `h_J(d + 1) ≤ h_J(d)^⟨d⟩`, where `h_J(e)` is the dimension of the degree-`e` part of `K[x]/J`.

Proof. Pass to leading monomials for a lexicographic order (`lex`, `LM`): the degree-`e` part of `J` and the span of
its leading monomials have the same dimension (`linearIndependent_of_degree_eq`, `card_LM_le`, `finrank_W`), and the
set of leading monomials is closed under multiplication by variables (`add_single_mem_LM`). So the monomials of
degree `d + 1` outside `LM(J)` all have their divisions outside `LM(J)` in degree `d`, and the ported combinatorial
bound `Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem` gives the claim (`finrank_piece_add`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.top`
- def `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.rem`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.macaulayPow_zero`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.macaulayPow_succ`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.sub_le_choose`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.choose_top_le`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.lt_choose_of_top_lt`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.lt_choose_top_succ`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.top_lt_of_lt_choose`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.le_top_of_choose_le`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.rem_add_choose`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.rem_lt`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.macaulayPow_lt_choose`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.macaulayPow_mono`
- def `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.Mon`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.mem_Mon`
- private def `MacaulayRed.lex`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.degree_eq_of_mem_support`
- def `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.LM`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.mem_LM`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.LM_subset`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.degree_mem_LM`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.add_single_mem_LM`
- def `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.W`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.mem_W`
- scoped instance `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.finite_homogeneousSubmodule`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.finrank_homogeneousSubmodule`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.finrank_W_le`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.linearIndependent_of_degree_eq`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.card_LM_le`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.finrank_W`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed.finrank_piece_add`
- theorem `P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem` (same contribution).
Other imports: `Mathlib`.
