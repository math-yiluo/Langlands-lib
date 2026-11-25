# The real equal-rank continuation step from a matched finite expansion

This internal reduction isolates the finite-product step in Hervé Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), §8.2, pp. 54–58. On pp. 55–57
the unfolded integral (8.1) becomes the sum (8.2) of adjacent-rank integrals
times square matrix integrals. On pp. 56 and 58 Jacquet gives the dual expansion,
with the factor from the removed character evaluated at `-1` to the power
`n - 1`. The determinant sign of the conclusion is the one in Theorem 2.1(iii)
(p. 6) and the sign calculation on p. 56, not the additional second-list sign
in the lower display on p. 53.

## Inputs and conclusion

In `RealLocalEqualJacquetExpansionReductionStatement` the matrix size is
`n = r + 2`, and the leading character `d` is separated from the real block
list `ds` of rank `n - 1`. The second list `es` has rank `n`. Allowing arbitrary
real blocks in `ds` and `es` is an internal generalization of the conditional
assembly in the principal-series argument; it asserts no expansion exists for
those lists.

* `AdjacentContinuationAtRank r` is the restriction of the uniform unequal-rank
  continuation premise to sizes `(n, n - 1)`. The second list of the equal-rank
  problem goes first in this adjacent-rank input.
* `HasEqualJacquetExpansion` requires the two half-plane identities for the
  actual `realEqualIntegral` and `realEqualDualIntegral (-a)`. Each summand uses
  the same compatible lower quotient datum and the same pair of uniform
  Whittaker coefficients in its primal and dual integrals, with additive
  parameters `-a` on the larger coefficient and `a` on the smaller one. This
  datum and pair may vary with the summand. The other factors are supplied
  meromorphic matrix continuations. Their equation
  (`PairMeromorphicIdentity [.character d] es (-a) 1`) uses the explicit inverse
  block lists, inverse reciprocal-entire denominators, and self-dual scale
  `sqrt ‖-a‖₊`. The expansion is required as an identity to the continuations on
  a common right half-plane; there is no formalized assertion here identifying
  those supplied factors with Godement–Jacquet integrals.
* The conclusion is `EqualContinuation a (-a)` with the explicit inverse
  block lists and the sign `determinant (.character d :: ds) (-1) ^ (n - 1)`.
  This package makes no claim about holomorphic multiples or vertical strips.

## Lean proof

The tensor block list for the leading character followed by `ds` splits as a
concatenation. The Library's product formulas therefore split both `L`
denominators and the epsilon factor. Pair-factor symmetry exchanges the two
lists in the adjacent equation. That equation initially has epsilon parameter
`a` because the larger coefficient has parameter `-a`; the matrix and target
equations both have epsilon parameter `-a`. The square-root scales agree under
negation. Writing `C_ds` and `C_es` for the respective determinants at `-1`,
the adjacent sign is `C_es ^ (n - 1) * C_ds`. The additive-character flip
contributes `C_ds ^ n * C_es ^ (n - 1)` by the tensor determinant identity.
Both determinant values square to one, as follows from the negation law for a
block determinant at `-1` and the determinant value at `1`. The two factors
reduce to `C_ds ^ (n - 1)`. With the Weyl factor `d(-1) ^ (n - 1)` already in
the dual expansion, this is the desired full determinant sign.

`pairMeromorphicIdentity_equal_sum_products` intersects the finitely many
codiscrete conditions and multiplies the two equations for each summand,
without cancelling a denominator at any point. The reduction theorem chooses
the adjacent continuations and takes the maximum of the expansion threshold
and an upper bound for the finitely many adjacent thresholds. The two sums of
products are meromorphic and agree with the original integrals on that right
half-plane.

The unfolding, justification of the half-plane identities, existence of the
matched matrix continuations, passage from the source's test and coefficient
classes to the Library's uniform model, and the adjacent-rank input all lie
outside this proof. This is not an unconditional proof of the positive equal-rank
statement `RealLocalUniformPositiveEqualContinuationStatement`.
