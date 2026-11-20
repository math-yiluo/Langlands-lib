# Integrability of the real block chart bound

`Langlands.Archimedean.realBlockChartIntegrable` proves
`Langlands.Archimedean.RealBlockChartIntegrableStatement`. It gives Lebesgue
integrability of the block chart bound on all real `k × a` matrices when
every tail sum of `ε_l + 1/2` is strictly negative.

## One-row estimate

The finitely many strict inequalities allow a common exponent `b < -1/2`
for which every tail sum of `ε_l - b` is nonpositive. For fixed `y`, the
logarithms of `1 + ∑_{i ≤ l} y_i²` are nonnegative and increasing in `l`.
Summation by parts pairs the successive differences of these logarithms
with the nonpositive tail sums of `ε_l - b`. Exponentiating bounds the
one-row product by the product with exponent `b` at every index.
`ParabolicChartBound.integrable_prod_one_add_sq_rpow` then gives an integrable
majorant `∏_l (1 + y_l²)^b`.

## Induction on the rows

Write the matrix as a first row `x` followed by `X'` and put
`S = I + X'ᵀ X'`. The proof rescales the rows of Mathlib's inverse LDL
factor by the inverse square roots of the positive diagonal entries,
obtaining a lower triangular `T` with `T S Tᵀ = I`. Triangularity preserves
this identity on each leading block and allows the same coordinate
change `y = x Tᵀ` to be used for all leading blocks. The rank-one
determinant lemma gives
`colGram [x; X'] l = colGram X' l · (1 + ∑_{i ≤ l} y_i²)`.

Deleting the first row shifts each row Gram index down by one. When `X'`
has at least one row, this gives the extra factor at index zero of `X'`,
which is `(det S)^{-1/2}` by `Matrix.det_one_add_mul_comm`. When `X'` has
zero rows the extra factor equals one. The identity `T S Tᵀ = I` gives
`|det(Tᵀ)⁻¹| = (det S)^{1/2}`.
`PartialJacquet.map_vecMulEquiv` supplies this change-of-variables factor
for Lebesgue measure, so the two powers of `det S` cancel.

The lower integral over `x` is therefore the bound at `X'` times the
finite lower integral of the one-row product. The Gram determinants are
positive and continuous, so the bound is nonnegative and continuous. Tonelli's
theorem and induction on `k` give integrability, with the constant-one
bound on the zero-row space as the base case. The proof also applies to
zero columns, where the column products and corresponding sums are empty.

## Provenance

This is an internal proof of the convergence input for the real block
Jacquet integral. It follows the row induction described in the target
statement and adapts the row reindexing and Tonelli argument from the
published complex proof. The one-row estimate uses the real product
integrability theorem and the strict tail conditions. [Target statement](RealBlockChartIntegralStatement.md),
[complex proof](ComplexBlockChartIntegralProof.md).
