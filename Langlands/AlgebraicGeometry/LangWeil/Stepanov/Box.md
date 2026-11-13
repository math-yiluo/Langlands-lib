# Degree boxes for bivariate polynomials

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`; not a result of the
literature.

Bivariate polynomials are represented as `F[X][Y] = Polynomial (Polynomial F)`: the outer
variable is `Y`, the inner variable (the coefficients) is `X`.

## Definition

`InBox a b P` (for integers `a b`) says that every monomial `X^i Y^j` that occurs in `P` has
`i ≤ a` and `j ≤ b`. Formally: for all `j i : ℕ`, if `(P.coeff j).coeff i ≠ 0` then
`(i : ℤ) ≤ a` and `(j : ℤ) ≤ b`. Integer bounds
are used so that the weighted filtrations of `Branch.lean`, whose bounds can be negative, fit
the same notion. Schmidt (*Zur Methode von Stepanov*, 1973) works with the same degree
conditions on the polynomials of his construction, stated separately for `X` and `Y`.

## Results

- `inBox_zero`, `InBox.mono`, `InBox.add`, `InBox.neg`, `InBox.sub`, `inBox_sum`: the box is a
  monotone family of additive subgroups.
- `InBox.mul`, `InBox.pow`, `inBox_prod`, `InBox.smul_C_C`: bounds add under multiplication.
- `inBox_C_C`, `inBox_one`, `inBox_C_X` (`X` lies in box `(1, 0)`), `inBox_X` (`Y` lies in box
  `(0, 1)`).
- `inBox_iff_of_nonneg`: for natural bounds, `InBox a b P` holds exactly when
  `P.natDegree ≤ b` and every coefficient has `natDegree ≤ a`.
- `InBox.eq_zero_of_neg_left`, `InBox.eq_zero_of_neg_right`: a negative bound forces `P = 0`.

All proofs are direct coefficient computations (`Polynomial.coeff_mul`, degree bounds of sums
and products).
