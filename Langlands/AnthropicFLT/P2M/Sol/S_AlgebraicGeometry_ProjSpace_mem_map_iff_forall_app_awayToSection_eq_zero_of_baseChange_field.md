# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 397, line 408 here): `← ProjSpace.awayMk_monomial k n i q α (hdeg α hα) (coeff α G), Away.val_mk]` is replaced by `← ProjSpace.awayMk_monomial k n i q α (hdeg α hα) (G.coeff α), Away.val_mk]`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 657, line 668 here): `let t : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) ⊗[k] K := ∑ α ∈ F.support.attach, (⟨MvPolynomial.monomial α.1 (1 : k), hmon α.1 α.2⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) ⊗ₜ[k] MvPolynomial.coeff α.1 F` is replaced by `let t : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) ⊗[k] K := ∑ α ∈ F.support.attach, (⟨MvPolynomial.monomial α.1 (1 : k), hmon α.1 α.2⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) ⊗ₜ[k] F.coeff α.1`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 659, line 670 here): `show β (∑ α ∈ F.support.attach, (⟨MvPolynomial.monomial α.1 (1 : k), hmon α.1 α.2⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) ⊗ₜ[k] MvPolynomial.coeff α.1 F) = F` is replaced by `show β (∑ α ∈ F.support.attach, (⟨MvPolynomial.monomial α.1 (1 : k), hmon α.1 α.2⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) ⊗ₜ[k] F.coeff α.1) = F`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 662, line 673 here): `rw [Finset.sum_attach F.support (fun α => MvPolynomial.monomial α (1 : K) * C (MvPolynomial.coeff α F))]` is replaced by `rw [Finset.sum_attach F.support (fun α => MvPolynomial.monomial α (1 : K) * C (F.coeff α))]`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field`. Statement. `AlgebraicGeometry.ProjSpace.mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field`: let `K / k`
be a field extension, `Z' ⊆ ℙⁿ_K` the base change of `Z ⊆ ℙⁿ_k` (affine embeddings), and `J` a homogeneous
ideal over `k` whose forms of degree `d ≥ m` are those vanishing on `Z`. Then the forms of degree `d ≥ m`
of the extended ideal `J K` are exactly those vanishing on `Z'`.

Proof. On the affine charts, sections of `Z'` are `K ⊗_k` sections of `Z` (ported
`Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback`, using
`ProjSpace.map_preimage_basicOpen_X`), and the dehomogenization of a form over `K` is the corresponding
`K`-combination of dehomogenizations over `k` (expanding in a `k`-basis of `K`). Since the forms of degree
`d` vanishing on `Z` form the subspace `J_d`, those vanishing on `Z'` form `K ⊗ J_d`, which is the degree-`d`
part of `J K` (linear algebra over fields: a vector of `K ⊗ V` maps to zero under `K ⊗ f` iff it lies in
`K ⊗ ker f`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.map_appTop_π_eq_awayToSection_algebraMap`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.val_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.frac_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.frac_smul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.awayMap_frac_eq`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.pullAway_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.pullAway_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.pullAway_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.pullAway_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.restrictFun_pullAway_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.restrictFun_pullAway_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.restrictFun_pullAway_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.pullAway_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.preimage_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.X_eq_mvMapGraded_mul_one`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.one_mem_zero`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.toB`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.toB_ratio`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.restrictFun_app_pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.restrictFun_app_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.restrictFun_app_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.appLE_top_top`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.appLE_hom_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.toB_mkDeg`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.dehom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.dehom_X`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.dehom_C`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.val_dehom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.dehom_eq_frac`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.chartHom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.chartHom_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.chartHom_eq_zero_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.toB_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.RM7Aux.toB_dehom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` (Library).
Other imports: `Mathlib`.
