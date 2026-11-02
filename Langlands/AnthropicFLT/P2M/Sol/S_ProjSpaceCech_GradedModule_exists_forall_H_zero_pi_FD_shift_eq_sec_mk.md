# `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 82, line 93 here): `coeff m (monomial u 1 * q) = if u ≤ m then coeff (m - u) q else 0 := by` is replaced by `(monomial u 1 * q).coeff m = if u ≤ m then q.coeff (m - u) else 0 := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 87, line 98 here): `have h1 : coeff (u + m) (monomial u 1 * q) = coeff m q := by` is replaced by `have h1 : (monomial u 1 * q).coeff (u + m) = q.coeff m := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 96, line 107 here): `∑ m ∈ q.support, monomial (m - u) (coeff m q)` is replaced by `∑ m ∈ q.support, monomial (m - u) (q.coeff m)`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 89, line 100 here): `have h2 := congrArg (coeff (u + m)) h` is replaced by `have h2 := congrArg ((·.coeff (u + m))) h`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk`. Statement. `ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk`: for a finite direct sum `F = ⊕ R[x](e_k)` of
shifted free graded modules over `R[x₀, …, x_n]`, there is `d₁` such that for all `d ≥ d₁` every class in the Čech `H⁰`
of the twist `F(d)` is represented by an element of `F` of degree `d` (global sections of `𝒪(d)` sums are polynomials).

Proof. Work componentwise (`toF`, `pi_monMul_apply`). A zero-cocycle is a compatible family of fractions
`f_j / x_jᵃ` on the charts; compatibility on the pairwise overlaps (`pairIdx`, `face_pairIdx_zero`, `face_pairIdx_one`)
forces each numerator to be divisible by the corresponding power of `x_j` (`le_add_of_monomial_mul_eq`, `divM`,
`monomial_mul_divM`), so all fractions come from a single homogeneous polynomial of degree `d` once `d` is large
enough relative to the shifts `e_k` (`divM_isHomogeneous`, `sec_mk_num_congr`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.toF`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.toF_apply`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.toF_add`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.toF_zero`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.prod_X_pow_eq`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.pi_monMul_apply`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.shift_monMul`
- abbrev `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.Fsh`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.monMul_Fsh_apply`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.monMul_Fsh_injective`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.coeff_monomial_one_mul`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.le_add_of_monomial_mul_eq`
- def `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.divM`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.monomial_mul_divM`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.divM_isHomogeneous`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.sec_mk_num_congr`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.mem_img_zero_iff`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.Idx_zero_ext`
- def `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.pairIdx`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.face_pairIdx_zero`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody.face_pairIdx_one`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library).
Other imports: `Mathlib`.
