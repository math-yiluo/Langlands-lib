# Pure product compact tests for a real standard module

`RealStandardCompactBlockProductStatement` starts with a finite list of
consecutive groups of inducing blocks. Given one compact-finite
standard vector in each group, it constructs a standard vector for the
concatenated parameter whose restriction to the compact block-diagonal
subgroup is the product of those vectors.

The proof expresses each compact restriction as a polynomial in the
entries of its smaller orthogonal matrix. It renames those entries by
their positions in the corresponding diagonal block and multiplies the
polynomials. On the block-diagonal subgroup, each sign change and each
inducing rotation acts in a single factor. Consequently the product
has the required sign covariance, and each low Fourier coefficient is
the corresponding zero local coefficient times the other factors.
The Library's compact projection fixes this restriction and supplies
the ambient standard vector.

This derived result gives pure product tests for comparison of
Hermitian forms in normalized induction in stages.
