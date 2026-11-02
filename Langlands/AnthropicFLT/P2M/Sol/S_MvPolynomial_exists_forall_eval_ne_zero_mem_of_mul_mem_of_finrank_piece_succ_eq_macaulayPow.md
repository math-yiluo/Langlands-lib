# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 304, line 316 here): `have hpC : p = C (coeff 0 p) := (totalDegree_eq_zero_iff_eq_C).mp (by` is replaced by `have hpC : p = C (p.coeff 0) := (totalDegree_eq_zero_iff_eq_C).mp (by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 350, line 362 here): `have h0 : homogeneousComponent 0 (c₀ i) = C (coeff 0 (homogeneousComponent 0 (c₀ i))) :=` is replaced by `have h0 : homogeneousComponent 0 (c₀ i) = C ((homogeneousComponent 0 (c₀ i)).coeff 0) :=`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 307, line 319 here): `have hc : coeff 0 p ≠ 0 := fun h => hp0 (by rw [hpC, h, C_0])` is replaced by `have hc : p.coeff 0 ≠ 0 := fun h => hp0 (by rw [hpC, h, C_0])`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 20 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (6 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow`. Statement. `MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow`: in the same setting, a
generic linear form `ℓ` is a nonzerodivisor modulo `J` in all degrees `k ≥ m`: if `f` is a form of degree `k ≥ m` with
`ℓ f ∈ J`, then `f ∈ J`.

Proof. The degree-`m` statement and maximal growth of `J + (ℓ)` come from the ported
`MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow`. Maximal growth means
the relations among the generators of `J` in degree `m + 1` are linear (`lp_of_maximal_growth`, `rel_mod_of_lp`);
section `SectionFamily` (`secF`) organizes the generators. Then the ported lemmas
`MvPolynomial.relation_mem_span_of_forall_isHomogeneous_mem_span`,
`MvPolynomial.relation_mem_span_of_linear_of_forall_relation_modulo_mem_span` and
`MvPolynomial.mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span` propagate the nonzerodivisor property
from degree `k` to `k + 1` (`main`, induction on `k`); Macaulay arithmetic is in the local `top`, `rem`, `macaulayPow`
lemmas.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.top`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.rem`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.macaulayPow_zero`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.macaulayPow_succ`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.sub_le_choose`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.choose_top_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.lt_choose_of_top_lt`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.lt_choose_top_succ`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.top_eq_of`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.le_top_of_choose_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.top_lt_of_lt_choose`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.d_le_top`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.top_zero_right`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.d_lt_top_of_pos`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.top_zero_left`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.rem_zero_left`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.rem_zero_right`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.rem_add_choose`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.rem_lt`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.macaulayPow_lt_choose`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.macaulayPow_mono`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.macaulayPow_zero_right`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Mac.lt_of_macaulayPow_add_le`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Ik`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.mem_Ik`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Ik_mono`
- scoped instance `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.finite_homogeneousSubmodule`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Jk`
- scoped instance `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.finite_Jk`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.finrank_piece_add`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.finrank_piece_eq_of_Ik_eq`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.mem_of_finrank_piece_eq_zero`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.decompose_eq`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.homogeneousComponent_mul_add`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.span_homogeneous`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.exists_eq_sum_X_mul`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.exists_eq_sum_mul_of_span`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.span_of_basis`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.homogeneous_of_gen`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.eq_top_of_zero`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.span_range_eq`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.isHomogeneous_linearForm`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.mem_span_of_mem`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.exists_eval_ne_zero`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.NU`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.uB`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.uB_hom`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.uB_span`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.secF`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.secF_left`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.secF_right`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.secF_hom`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.le_secF`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.secF_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.Ik_secF`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.finrank_piece_secF`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.rel_mod_of_lp`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.lp_of_maximal_growth`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.GotzRegW2.main`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_relation_mem_span_of_linear_of_forall_relation_modulo_mem_span` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span` (same contribution).
Other imports: `Mathlib`.
