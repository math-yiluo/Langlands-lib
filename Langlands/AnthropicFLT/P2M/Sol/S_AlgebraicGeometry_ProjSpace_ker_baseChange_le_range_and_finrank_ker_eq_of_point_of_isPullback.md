# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 347, line 358 here): `ε 0 ((Θ₀.baseChange K) t) = cK ⟨MvPolynomial.monomial α (MvPolynomial.coeff α F), by` is replaced by `ε 0 ((Θ₀.baseChange K) t) = cK ⟨MvPolynomial.monomial α (F.coeff α), by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 355, line 366 here): `refine ⟨MvPolynomial.coeff α F ⊗ₜ[A₀] ⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩, ?_⟩` is replaced by `refine ⟨F.coeff α ⊗ₜ[A₀] ⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩, ?_⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 356, line 367 here): `have hc : MvPolynomial.coeff α F ⊗ₜ[A₀] (⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩ :` is replaced by `have hc : F.coeff α ⊗ₜ[A₀] (⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩ :`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 358, line 369 here): `= MvPolynomial.coeff α F • ((1 : K) ⊗ₜ[A₀] ⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩) := by` is replaced by `= F.coeff α • ((1 : K) ⊗ₜ[A₀] ⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 373, line 384 here): `show ∑ α ∈ F.support.attach, MvPolynomial.monomial α.1 (MvPolynomial.coeff α.1 F) = F` is replaced by `show ∑ α ∈ F.support.attach, MvPolynomial.monomial α.1 (F.coeff α.1) = F`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 374, line 385 here): `rw [Finset.sum_attach F.support (fun α => MvPolynomial.monomial α (MvPolynomial.coeff α F))]` is replaced by `rw [Finset.sum_attach F.support (fun α => MvPolynomial.monomial α (F.coeff α))]`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 363, line 374 here): `show MvPolynomial.coeff α F • MvPolynomial.map (algebraMap A₀ K) (MvPolynomial.monomial α 1) = MvPolynomial.monomial α (MvPolynomial.coeff α F)` is replaced by `show F.coeff α • MvPolynomial.map (algebraMap A₀ K) (MvPolynomial.monomial α 1) = MvPolynomial.monomial α (F.coeff α)`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback`. Statement. `AlgebraicGeometry.ProjSpace.ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback`: let
`Z_K ⊆ ℙⁿ_K` be the base change of `Z₀ ⊆ ℙⁿ_{A₀}` to a field `K`, `d ∈ ℕ`, `Θ₀` the dehomogenization map of
`Z₀` in degree `d`, and `q` a point over `K` with Hilbert function `h` whose forms of degree `d` are those
vanishing on `Z_K`. If the higher Čech cohomology of `𝒪_{Z_K}(d)` vanishes and every `H⁰` class comes
from a form, then after base change to `K` the Čech complex of `𝒪_{Z₀}(d)` is exact in positive
degrees, the kernel of the first differential lies in the image of `Θ₀ ⊗ K`, and this kernel has
dimension `h d`.

Proof. The Čech complex of `Z_K` is the base change of that of `Z₀` (ported
`ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback`, with the chart compatibilities of
`ProjSpace.map_preimage_basicOpen_X`), so vanishing of the cohomology of `Z_K` is exactness of the
base-changed complex, and `H⁰(Z_K)` is the kernel of the base-changed first differential. Dehomogenization
commutes with base change (ported `ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq`),
so the hypothesis on `H⁰` gives the inclusion in the image of `Θ₀ ⊗ K`; the kernel of `Θ_K` consists of
the forms of `q.I`, so `H⁰(Z_K) ≅ piece q.I d` has dimension `h d`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.X_eq_mvMapGraded_mul_one`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.one_mem_zero`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.toB`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.toB_ratio`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.restrictFun_app_pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.restrictFun_app_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.restrictFun_app_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.preimage_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.preimage_inter`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.toB_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.P2mWs6K4C.subsingleton_HSucc_iff`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library).
Other imports: `Mathlib`.
