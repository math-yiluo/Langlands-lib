# The degree of an endomorphism is a determinant: conclusion

This module proves `Langlands.Algebra.DegreeDeterminant.DegreeData.det_eq`. It defines nothing new.

## Main result

`DegreeData.det_eq`: for a ring `R`, `ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]`, `δ : R → ℚ` and `iso : R → Prop` with `DegreeData ρ δ iso` (module `Core`), and every `α : R`,

`(δ α : ℚ_[p]) = (ρ α).det`.

This is the algebraic part of Milne's proof of Proposition 12.9 (*Abelian Varieties*, author revision 2022, pp. 23–24).

## Helper results

- `det_aeval_eq_prod_roots`: for a `2g × 2g` matrix `A` over an algebraically closed field, `det (F(A)) = ∏ F(q)` over the roots `q` of `charpoly A`. This is `eq_prod_eval_roots` (module `MultiplicativeRoots`) for `Φ F = det (F(A))`. `det (A - x) = charpoly A (x)` because the size `2g` is even.
- `exists_integral_multiple`: every `π : ℚ_[p][X]` has a multiple `C c * π` with `c = p ^ N ≠ 0` whose coefficients have norm at most `1`.
- `coeffEval_add_C_eq`: `t ↦ coeffEval M (F + C t)` is the evaluation of an explicit one-variable polynomial.
- `coeffEval_map_algebraMap`: compatibility of `coeffEval` with `algebraMap S T` for a scalar tower `ℚ → S → T`.
- `norm_coeffEval_eq`: for `F` over `ℚ_[p]` of degree `< N` with integral coefficients and `det (F(ρ α)) ≠ 0`, `‖coeffEval M F‖ = ‖det (F(ρ α))‖`. This is `norm_eval_eq_of_natCast` (module `PadicComparison`) applied to `M` and to `edet (ρ α)`. At natural points, `norm` and `zero` of `DegreeData` give the hypothesis.

## Proof of `DegreeData.det_eq`

Let `M` be given by `DegreeData.exists_mvPolynomial` with `N = 2 * (2 * g + 1) + 1`, let `A = ρ α`, and let `L` be the algebraic closure of `ℚ_[p]` with `A_L` the image of `A`.

1. Lemma 12.11 for `δ`: by `coeffEval_mul`, `coeffEval_C` and `lineQ_monic`, `eq_prod_eval_roots` gives `coeffEval M F = ∏ F(q)` over the roots of `lineQ M` in `L`, for `F` over `L` of degree at most `2g + 1`.
2. Lemma 12.11 for the determinant: `det (F(A_L)) = ∏ F(q)` over the roots of `charpoly A` in `L`.
3. Root counts. Let `π` be monic irreducible over `ℚ_[p]` of degree at most `2g + 1`, and let `π' = C c * π` be integral. Let `u(t) = coeffEval M (π' + C t)` and `v(t) = det ((π' + C t)(A))`. Both are polynomials in `t`; `v` is `charpoly (-π'(A))`. By steps 1 and 2, over `L` they become `∏ (X + C (π'(q)))` over the roots of `lineQ M` and of `charpoly A` respectively. So by `rootMultiplicity_zero_prod` their orders of vanishing at `0` are `rootCount L (lineQ M) π` and `rootCount L (charpoly A) π`. By `norm_coeffEval_eq`, `‖u(t)‖ = ‖v(t)‖` whenever `‖t‖ ≤ 1` and `v(t) ≠ 0`. `rootMultiplicity_zero_eq_of_norm_eval_eq` then makes the two orders equal.
4. `eq_of_rootCount_eq` gives `lineQ M = charpoly A` over `ℚ_[p]`.
5. With `F = X` in steps 1 and 2, `coeffEval M X = det A_L`. Over `ℚ_[p]`, `coeffEval M X = δ α` by `coeffEval_natCast`. Injectivity of `ℚ_[p] → L` gives `δ α = det A`.

## Provenance

Milne's proof of Proposition 12.9 shows `|∏ F(a_i)|_l = |deg F(α)|_l = |det T_l(F(α))|_l = |∏ F(b_i)|_l` for all `F ∈ ℤ[T]` and concludes by Lemma 12.10. Steps 3 and 4 are an internal proof of that conclusion. They use only polynomials `π' + C t` and the root counts of module `MultiplicativeRoots`, in place of Lang's lemma.
