# Column-degree bound for the Sylvester resultant over `R[X]`

Module `Langlands.AlgebraicGeometry.LangWeil.Stepanov.ResultantDegree`. It imports only
Mathlib (`Mathlib.RingTheory.Polynomial.Resultant.Basic`).

## Statements

In both statements, `R` is a commutative ring.

- `natDegree_det_le_sum_of_col`: let `M` be a square matrix over `R[X]`, indexed by a finite
  type with decidable equality. If every entry in column `b` has `natDegree ≤ c b`, then
  `M.det.natDegree ≤ ∑ b, c b`. This is an auxiliary lemma.
- `resultant_natDegree_le` (main result): let `p r : Polynomial (Polynomial R)` and
  `a b mp mr : ℕ`. Suppose every coefficient of `p` has `natDegree ≤ mp` and every
  coefficient of `r` has `natDegree ≤ mr`. Then
  `(Polynomial.resultant p r a b).natDegree ≤ b * mp + a * mr`.

## Provenance

This is a standard estimate for the Sylvester determinant. It is internal to the project, not
quoted from a source. It is used for the discriminant good set in the Stepanov–Schmidt argument
(W. M. Schmidt, *Zur Methode von Stepanov*, Acta Arithmetica 24 (1973)); see
`Langlands.AlgebraicGeometry.LangWeil.Stepanov.GoodSet`. Mathlib's `sylvester p r a b` has
`a` columns of coefficients of `r` followed by `b` columns of coefficients of `p`. Every term of
the Leibniz expansion of its determinant therefore has degree at most `b * mp + a * mr`. Zero
entries do not affect the bound.

## Proof

- **Determinant.** `Matrix.det_apply'` writes `det M` as a sum over permutations `τ` of
  `sign τ * ∏ b, M (τ b) b`.
  - The sign is an integer cast, so it has degree `0` (`natDegree_intCast`).
  - `natDegree_prod_le` and `Finset.sum_le_sum` bound the product by `∑ b, c b`.
  - `natDegree_sum_le_of_forall_le` bounds the sum.
- **Resultant.** `resultant p r a b` is by definition `det (sylvester p r a b)`. Apply the
  determinant bound with column bounds `Fin.addCases (fun _ => mr) (fun _ => mp)`.
  - Each entry of the Sylvester matrix is a coefficient of `r` (first `a` columns), a
    coefficient of `p` (last `b` columns), or zero. This is checked by unfolding `sylvester`
    and splitting the `if`.
  - `Fin.sum_univ_add` evaluates the sum of column bounds to `a * mr + b * mp`, and `ring`
    reorders it.
