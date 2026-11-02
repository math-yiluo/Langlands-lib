# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 67, line 79 here): `· rw [coeff_zero, coeff_mul]` is replaced by `· rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, coeff_mul]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 91, line 103 here): `· rw [coeff_zero]` is replaced by `· rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 51, line 63 here): `have hpdeg : ∀ α : σ →₀ ℕ, coeff α p ≠ 0 → Finsupp.degree α = k := fun α hα => by` is replaced by `have hpdeg : ∀ α : σ →₀ ℕ, p.coeff α ≠ 0 → Finsupp.degree α = k := fun α hα => by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line None, line 71 here): `by_cases hα : coeff x.1 p = 0` is replaced by `by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 83, line 95 here): `· by_cases hα : coeff x.1 p = 0` is replaced by `· by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 131, line 143 here): `have hmono : monomial μ (coeff μ (c j)) = C (coeff μ (c j)) * monomial (μ - ν) (1 : A) * monomial ν 1 := by` is replaced by `have hmono : monomial μ ((c j).coeff μ) = C ((c j).coeff μ) * monomial (μ - ν) (1 : A) * monomial ν 1 := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 134, line 146 here): `have : MvPolynomial.map ψ (gen j) * monomial μ (coeff μ (c j)) =` is replaced by `have : MvPolynomial.map ψ (gen j) * monomial μ ((c j).coeff μ) =`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 135, line 147 here): `(C (coeff μ (c j)) * monomial (μ - ν) (1 : A)) * (monomial ν 1 * MvPolynomial.map ψ (gen j)) := by` is replaced by `(C ((c j).coeff μ) * monomial (μ - ν) (1 : A)) * (monomial ν 1 * MvPolynomial.map ψ (gen j)) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line None, line 82 here): `by_cases hα : coeff x.1 p = 0` is replaced by `by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 20 here); in 23 lines the replacements `Type` (universe 0) → `Type uz` (21 places), `Scheme.{0}` → `Scheme.{uz}` (3 places), `Type` → `Type*` (a fresh universe; 1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg`:
let `Hilb ⟶ Spec R` represent the points of the Hilbert functor with Hilbert function `h` over
`R`-algebras (an equivalence `pt A ψ` between points over `A` and `A`-points of `Hilb` over `ψ`,
natural in base change, with points stable under base change). For a finitely generated homogeneous
ideal `I₀` of `R[X₀, …, Xₙ]` and `m ∈ ℕ`, there is a closed immersion `ι : C ⟶ Hilb`, locally of finite
presentation, such that an `A`-point `pt A ψ P` factors through `C` iff every form of degree `≥ m` in
the extension of `I₀` lies in `P.I` (the locus of subschemes containing `I₀` in degrees `≥ m`).

Proof (namespaces `P2Aux`, `P2R`, `HilbR`). Write `I₀` as the span of the homogeneous components
`gen j` (degree `deg j`) of finitely many generators. `P2R.forall_mem_iff_of_span`: the condition is
equivalent to finitely many memberships: `monomial μ · gen j ∈ P.I` for the monomials `μ` of degree
`max m (deg j) - deg j` (using `P2Aux.exists_le_degree_eq` and `homogeneousComponent_mul_left`).
Each membership condition is the vanishing of the class of a form in the finite projective piece
`piece P.I d`, a condition that is Zariski local and compatible with base change. The ported theorem
`exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut` (closed
subschemes cut out by finitely many such conditions on a functor of points) gives `C`, after checking
compatibility with base change and Zariski descent along covers by `Localization.Away`
(`HilbR.ringHom_eq_of_specMap_eq`, `HilbR.exists_ringHom`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.P2Aux.exists_le_degree_eq`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.P2Aux.homogeneousComponent_mul_left`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.P2R.forall_mem_iff_of_span`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.HilbR.ringHom_eq_of_specMap_eq`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.HilbR.exists_ringHom`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway` (same contribution).
Other imports: none.
