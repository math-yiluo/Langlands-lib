# `Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 121, line 133 here): `theorem coeff_lin_single (a : Fin M → K) (i : Fin M) : coeff (Finsupp.single i 1) (lin a) = a i := by` is replaced by `theorem coeff_lin_single (a : Fin M → K) (i : Fin M) : (lin a).coeff (Finsupp.single i 1) = a i := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 172, line 184 here): `p = lin (fun i => coeff (Finsupp.single i 1) p) := by` is replaced by `p = lin (fun i => p.coeff (Finsupp.single i 1)) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 178, line 190 here): `· have h1 : coeff s p = 0 := by` is replaced by `· have h1 : p.coeff s = 0 := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 181, line 193 here): `have h2 : coeff s (lin fun i => coeff (Finsupp.single i 1) p) = 0 := by` is replaced by `have h2 : (lin fun i => p.coeff (Finsupp.single i 1)).coeff s = 0 := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 421, line 433 here): `have hcoeff : coeff d r ≠ 0 := mem_support_iff.mp hd` is replaced by `have hcoeff : r.coeff d ≠ 0 := mem_support_iff.mp hd`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 618, line 630 here): `set b : Fin (N + 1) → K := fun i => coeff (Finsupp.single i 1) p with hb` is replaced by `set b : Fin (N + 1) → K := fun i => p.coeff (Finsupp.single i 1) with hb`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 137, line 149 here): `rw [h0, coeff_zero] at this` is replaced by `rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 570, line 582 here): `rw [coeff_zero]` is replaced by `rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 17 here); in 7 lines the replacements `Type` (universe 0) → `Type uz` (7 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le`. Statement. `MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le` (a hyperplane restriction inequality):
let `J` be a homogeneous ideal of `K[x₀, …, x_n]` over an infinite field and `d ≥ 1`; write `h_I(d)` for the dimension
of the degree-`d` part of `K[x]/I` and `a^⟨d⟩` for `Nat.macaulayPow d a`. There is a nonzero polynomial `G` such that
for every linear form `ℓ = Σ aᵢ xᵢ` with `G(a) ≠ 0`, `h_{J+(ℓ)}(d)^⟨d⟩ + h_J(d) ≤ h_J(d)^⟨d⟩`.

Proof. Section `SemiCont`: the relevant ranks of linear maps depending polynomially on `a` attain their generic
values outside a hypersurface (`exists_generic_rank`, `exists_generic_codim`, `exists_eval_ne_zero`). Sections
`Pieces`, `Restrict`: after a linear change of coordinates moving `ℓ` to the last variable (`θ`, `φ`, `pull`),
`K[x]/(J + ℓ)` is a quotient of a polynomial ring in one variable fewer (`map_φ_eq`, `codim_map_φ`). Section
`Kernel`: the multiplication by `ℓ` from degree `d - 1` to degree `d` has kernel computed by colon ideals
(`mulSub`, `codim_eq_colon_add`, `finrank_ker_gA`). Section `Main`: induction on the number of variables
(`HS_zero_vars`, `main`), using the arithmetic inequality of the ported
`Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add`. Section `Ideals` relates the pieces of sums of ideals
(`finrank_piece_eq_codim`, `HS_inf_sup_span`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.fam`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.fam_apply`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.exists_generic_rank`
- abbrev `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.HS`
- scoped instance `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finite_HS`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin_isHomogeneous`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin_mem`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.coeff_lin_single`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin_ne_zero`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin_zero`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin_add`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin_smul`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.lin_single`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.exists_eq_single_of_degree_eq_one`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.eq_lin_of_mem_one`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.mulSub`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.mul_mem_mulSub`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.mem_mulSub_iff`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.mulSub_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_mulSub`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.mulSub_zero`
- scoped instance `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finite_mulSub`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.codim`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_le_of_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_map_add`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_sup_eq`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_sup_mulSub_add`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.codim_eq_colon_add`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.exists_generic_codim`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.exists_eval_ne_zero`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.bvec`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.θ`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.θ_castSucc`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.θ_last`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.θ_isHomogeneous`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ_mem`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.map_φ_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ_rename`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.map_φ_eq`
- scoped instance `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finite_map_φ`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ_X_castSucc`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ_X_last`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.algHom_lin`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.Lmap`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ_lin`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.Lmap_self`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ_lin_self`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.Lmap_snoc`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.pull`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.eval_pull`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.pull_ne_zero`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.mem_mulSub_X_of_φ_eq_zero`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.gA`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_ker_gA`
- def `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.BA`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.BA_le_ker`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_BA`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_HS_succ`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.φ_eq_zero_iff`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.codim_map_φ`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.map_mulSub`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.map_colon_le`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.macaulayPow_one`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.HS_zero_vars`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.main`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.finrank_piece_eq_codim`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.decompose_eq`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.homogeneousComponent_mul_add`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT.HS_inf_sup_span`
- theorem `P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add` (same contribution).
Other imports: `Mathlib`.
