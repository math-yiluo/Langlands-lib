# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 27, line 39 here): `have hpdeg : ∀ α : σ →₀ ℕ, coeff α p ≠ 0 → Finsupp.degree α = k := fun α hα => by` is replaced by `have hpdeg : ∀ α : σ →₀ ℕ, p.coeff α ≠ 0 → Finsupp.degree α = k := fun α hα => by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line None, line 47 here): `by_cases hα : coeff x.1 p = 0` is replaced by `by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 59, line 71 here): `· by_cases hα : coeff x.1 p = 0` is replaced by `· by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 43, line 55 here): `· rw [coeff_zero, coeff_mul]` is replaced by `· rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, coeff_mul]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line 67, line 79 here): `· rw [coeff_zero]` is replaced by `· rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]`. In the project's Mathlib the lemma `MvPolynomial.coeff_zero` (FLT: `coeff m 0 = 0`) is replaced by `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; it is followed by `Finsupp.coe_zero` and `Pi.zero_apply` to evaluate at `m`, which gives the FLT rewrite.
- Manual edit for Mathlib drift (FLT line None, line 58 here): `by_cases hα : coeff x.1 p = 0` is replaced by `by_cases hα : p.coeff x.1 = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 15 here); in 2 lines the replacements `Type` (universe 0) → `Type uz` (2 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero`. Statement. `AlgebraicGeometry.HilbertFunctor.map_mem_iff_tmul_mkQ_piece_eq_zero`: let `φ : B → A` be a ring map,
`P` a Hilbert point over `B` and `Q` one over `A` with `Q.I = φ(P.I)`. For a form `F` of degree `d` over
`B`, `φ(F) ∈ Q.I` iff `1 ⊗ [F] = 0` in `A ⊗[B] piece P.I d`.

Proof (namespace `P1Aux` for graded lemmas). Let `S e` be the `A`-span of the images of the forms of
degree `e` in `P.I`, and `T` the ideal of polynomials whose components lie in the `S e` (closed under
multiplication by constants and variables, hence an ideal containing `Q.I`). So `φ(F) ∈ Q.I` puts
`φ(F)` in `S d`; under the identification `A ⊗[B] (forms of degree d) ≅ forms of degree d over A`, `S d`
lies in the image `W` of `A ⊗ (P.I)_d`, whose image in `A ⊗ piece P.I d` is zero (right exactness of
`A ⊗ -`). Conversely, `1 ⊗ [F] = 0` means `1 ⊗ F` lies in the image of `A ⊗ (P.I)_d`, so `φ(F)` is an
`A`-combination of images of elements of `P.I`, hence in `Q.I`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.P1Aux.homogeneousComponent_map`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.P1Aux.homogeneousComponent_mul_left`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution).
Other imports: none.
