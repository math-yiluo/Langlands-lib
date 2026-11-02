# The actual smaller Laurent identity on dominant first-block fibers

This is derived infrastructure for JPSS (1983), §4.9, printed pp.416–418,
and §4.10(2), printed p.419. For positive block sizes `a=m 0+1`, `b=m 1+1`
and arbitrary complementary `j,k`, the smaller integral has row counts
`b+j,k`. The field, test carrier and block carrier universes are independent.

`firstBlockReflectedSmallCoefficient` multiplies the actual reflected dual
smaller determinant-slice coefficient by the base determinant factor
`|det g|^(- (j+k+1)/2+j)`. Its large test is the translated supplied test by
the remaining second-block columns and the leading inclusion of `g`;
its small test is the actual first-block coefficient of the section at `g`.
It uses the exact supplied scalar rectangle and compatible small quotient
measures. Its definition does not assert convergence or identify a lower kernel.

`firstBlock_small_laurent_identity` assumes full Whittaker type for the large
test and first block, the actual two normalized-generator polynomials, and
common normalized functional equations for all pairs of coefficient-model
vectors at these row counts. At every `Y,g` it proves that the reflected
dual polynomial acting on this reflected smaller coefficient equals the
epsilon monomial and the original polynomial acting on the actual upper
first-block coefficient.

The original normalized generator forces both supplied functionals to be
nonzero within this conditional certificate clause. The two actual small
integrals have separate absolutely convergent determinant-slice expansions
on their own right half-planes. The published spectral uniqueness and finite
reflection bridge therefore give the identity without cancelling any
polynomial on a bilateral series. The existing upper disintegration identifies
the original smaller coefficient with the actual upper coefficient, and
commuting the common base scalar through finite convolution completes the
proof. No irreducibility or nonvanishing condition is added outside the
certificate clause. Identifying the reflected coefficient with the actual
lower kernel and integrating over the remaining columns and outer quotient
are separate consumer obligations.
