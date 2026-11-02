# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 292, line 304 here): `(p ∈ J ↔ ∀ m ∈ D, coeff m p = 0)) :` is replaced by `(p ∈ J ↔ ∀ m ∈ D, p.coeff m = 0)) :`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 298, line 310 here): `{ toFun := fun p m => coeff m.1 p.1` is replaced by `{ toFun := fun p m => p.1.coeff m.1`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 301, line 313 here): `have hφ : ∀ (p : ↥V) (m : ↥D), φ p m = coeff m.1 p.1 := fun _ _ => rfl` is replaced by `have hφ : ∀ (p : ↥V) (m : ↥D), φ p m = p.1.coeff m.1 := fun _ _ => rfl`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line None, line 405 here): `· rintro rfl m _; exact coeff_zero m` is replaced by `· rintro rfl m _; simp`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`, used here as a term) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; the goal `(0 : MvPolynomial _ _).coeff m = 0` is closed by `simp`.
- Manual edit for Mathlib drift (FLT line None, line 408 here): `rw [coeff_zero]` is replaced by `rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line None, line 509 here): `· rintro rfl m _; exact coeff_zero m` is replaced by `· rintro rfl m _; simp`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`, used here as a term) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; the goal `(0 : MvPolynomial _ _).coeff m = 0` is closed by `simp`.
- Manual edit for Mathlib drift (FLT line None, line 512 here): `rw [coeff_zero]` is replaced by `rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 18 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (6 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow`. Statement. `MvPolynomial.mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow`: an ideal `J` generated in degree
`m ≥ 1` with maximal growth is saturated in degrees `≥ m`: if `F` is a form of degree `d ≥ m` with `xᵢᴺ F ∈ J` for all
`i`, then `F ∈ J`.

Proof. Section `Sat`: let `J^sat` be the saturation (`sat`, `mem_sat`, `sat_homogeneous`). It agrees with `J` in large
degrees, so their Hilbert functions agree eventually. By persistence (ported
`MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow`) `h_J` grows maximally from
degree `m` on, while `h_{J^sat}` is bounded by Macaulay's theorem (ported `MvPolynomial.finrank_piece_succ_le_macaulayPow`)
and is `≤ h_J`; strict monotonicity of Macaulay powers (`macaulayPow_strictMono`, `le_of_macaulayPow_le`) then forces
`h_{J^sat}(d) = h_J(d)` for `d ≥ m`, so `J^sat` and `J` agree in these degrees (`Ipart_eq_of_le_of_finrank_eq`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.top`
- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.rem`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_zero`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_succ`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.sub_le_choose`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.choose_top_le`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.lt_choose_of_top_lt`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.lt_choose_top_succ`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.le_top_of_choose_le`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.top_lt_of_lt_choose`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.d_le_top`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.rem_add_choose`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.rem_lt`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.top_zero_left`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.rem_zero_left`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.top_zero_right`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.rem_zero_right`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_zero_right`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_lt_choose`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_mono`
- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.Mon`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.mem_Mon`
- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.MonW`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.mem_MonW`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.MonW_mono`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.MonW_of_le`
- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.var`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.var_apply`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.degree_var`
- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.shift`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.shift_of_le`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.mem_shift`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.card_shift`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.shift_empty`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.shift_mono`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.sub_var_add_var`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.add_var_sub_var`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.mem_shift_iff`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.degree_sub_var`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.MonW_succ`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.disjoint_MonW_shift`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.MonW_zero_succ`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.MonW_zero_right`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.card_MonW`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.card_Mon`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.degree_eq_of_mem_support`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.finrank_piece_eq_card`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_one`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_lt_succ`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_strictMono`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.le_of_macaulayPow_le`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.top_eq_of'`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.macaulayPow_choose`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.finrank_piece_le`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.homogeneousComponent_mem_of_span`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.hc_eq`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.hc_mul_left`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.hc_mul_right`
- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.sat`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.mem_sat`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.le_sat`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.pow_mul_mem_of_le`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.sat_homogeneous`
- def `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.Ipart`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.mem_Ipart`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.finite_homog`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.finrank_piece_add`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.finrank_piece_le_of_le`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.Ipart_eq_of_le_of_finrank_eq`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.exists_le_of_degree_ge`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.mul_mem_of_saturated`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.hc_mul_mem`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.SATSOL.eventually_mem`
- theorem `P2MW.S_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow` (same contribution).
Other imports: `Mathlib`.
