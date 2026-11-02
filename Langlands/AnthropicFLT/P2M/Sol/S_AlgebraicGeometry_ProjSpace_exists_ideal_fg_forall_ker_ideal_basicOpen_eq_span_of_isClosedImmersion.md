# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 59, line 71 here): `· rw [coeff_zero, coeff_mul]` is replaced by `· rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, coeff_mul]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 83, line 95 here): `· rw [coeff_zero]` is replaced by `· rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 43, line 55 here): `have hpdeg : ∀ α : σ →₀ ℕ, coeff α p ≠ 0 → Finsupp.degree α = k := fun α hα => by` is replaced by `have hpdeg : ∀ α : σ →₀ ℕ, p.coeff α ≠ 0 → Finsupp.degree α = k := fun α hα => by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line None, line 63 here): `by_cases hα : coeff x.1 p = 0` is replaced by `by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 75, line 87 here): `· by_cases hα : coeff x.1 p = 0` is replaced by `· by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line None, line 74 here): `by_cases hα : coeff x.1 p = 0` is replaced by `by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 18 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (4 places), `Scheme.{0}` → `Scheme.{uz}` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion`. Statement. `AlgebraicGeometry.ProjSpace.exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion`:
for a closed immersion `ι : Z ⟶ ℙⁿ_A` with `Z` locally of finite presentation over `Spec A`, there is a
finitely generated homogeneous ideal `I₀` of `A[X₀, …, Xₙ]` whose dehomogenizations generate the ideal
of `Z` on every standard chart.

Proof (namespace `IdealFGAux`). On each chart the ideal of `Z` is finitely generated, since the chart
ring is of finite type over `A` and `Z` is of finite presentation over it
(`finitePresentation_app_of_comp`, `ker_ideal_fg_of_finitePresentation_app`). Each generator is
`F / Xᵢ^d` for a form `F`; let `I₀` be generated by the homogeneous components of all these numerators
(finitely many, `exists_finite_subset_le_span`, `exists_finite_subset_image`,
`homogeneousComponent_mem_span`). The ported `ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span`
and a chart-wise comparison show that the dehomogenizations of `I₀` generate exactly the ideal of
`Z` on each chart.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.IdealFGAux.exists_finite_subset_le_span`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.IdealFGAux.exists_finite_subset_image`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.IdealFGAux.homogeneousComponent_mul_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.IdealFGAux.homogeneousComponent_mem_span`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.IdealFGAux.ker_ideal_fg_of_finitePresentation_app`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.IdealFGAux.finitePresentation_app_of_comp`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion` (same contribution).
Other imports: `Mathlib`.
