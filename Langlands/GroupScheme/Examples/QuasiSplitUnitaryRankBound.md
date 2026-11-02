# The split-rank upper bound for U(1,1)

Workers 1225 and 37. This internal argument derives the split-rank upper
bound from the existing unitary matrix model. The fields, quadratic extension,
finite matrix basis, and automorphism are those of `RankStatement`. No
nonidentity hypothesis on the automorphism is needed for this bound, and the
argument works in every characteristic. The auxiliary index type `I` has a
chosen finite enumeration and decidable equality; the final proof obtains
these from its `Finite I` hypothesis.

For a homomorphism from the actual split torus, let `P` be `splitTorusUniversalMatrix`,
the matrix of the image of its universal point over `F[ℤ^I]`, with tensor
coefficients transported to `E[ℤ^I]`. The exponent maps into the two independent
factors give the multiplicativity hypothesis of `RankCoefficients.matrixCoeff_mul`.
Consequently `universalMatrix_coeff_mul` proves that the coefficient matrices
are pairwise orthogonal idempotents. Taking coefficients of the published
conjugate-adjoint identity gives `universalMatrix_coeff_neg`: the coefficient
at `-a` is the coefficient at `a` with reversed transposed indices and conjugated
entries. This makes nonzero support stable under negation.

The support lemma for orthogonal projections bounds the number of nonzero
coefficient matrices by two. A negation-stable set of at most two integer
vectors lies in one opposite pair, so `universalMatrix_support_in_pair`
places every occurring weight in `{a,-a}`. The absence of nonzero integer
2-torsion is used only in this lattice argument, independently of the
characteristic of either field.

`groupAlgebraMatrixCoordinates_injective` cancels the scalar tensor equivalence
entrywise and then applies injectivity of the affine matrix coordinates.
`universalMatrix_map_eq_zeroMap` says that an exponent map vanishing on every
occurring weight gives the same matrix as the zero exponent map. It uses
`Finsupp.mapDomain_congr` on the support of each matrix entry; a nonzero entry
coefficient forces its coefficient matrix to be nonzero. The zero exponent
map sends the universal torus point to the identity. Conversely, if an exponent
map sends that point to the identity, every coordinate exponent is zero:
`universalPoint_exponentMap_eq_one` checks unit coordinates and uses injectivity
of a monomial's exponent over the nonzero field `F`.

Finally `splitTorus_rank_le_one` argues by contradiction when `Nat.card I ≥ 2`.
The elementary integer-kernel lemma supplies `m ≠ 0` with
`∑ j, a j * m j = 0`. Define an exponent map by
`d ↦ ∑ j, d j * m j`, with its integer target lifted to universe `u`.
Thus the resulting point is valued in a one-variable group algebra, with
coordinates the Laurent monomials of exponents `m j`. The map kills both
`a` and `-a`, hence every occurring weight, so the universal image matrix
becomes the constant identity specialization. Matrix-coordinate injectivity
makes the corresponding image points equal. Since the given homomorphism
is a closed immersion, its underlying morphism is a monomorphism; cancellation
then makes the specialized torus point itself the identity. Its coordinate
exponents must all vanish, contradicting `m ≠ 0`.

This proves claim 2 of the unchanged `RankStatement`. The cocharacter closedness
and the rank-two split torus after base change are supplied by separate modules.
