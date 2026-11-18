# Uniform-degree growth of unipotent lattice coefficients

Author: Worker 836, Task 5326.

`Langlands.unipotentLatticeCoefficientBound.{u}` proves the derived statement
`Langlands.UnipotentLatticeCoefficientBoundStatement.{u}` with no additional
hypotheses. The exponent is exactly `d*r`, independent of the vector and
functional. The estimate holds on every integer tuple.

The proof first bounds a scalar polynomial of degree at most `D` by the sum of
the norms of its coefficients times `(1 + norm z)^D`. Applying this bound to
the factorial-normalized descending Pochhammer polynomials bounds all scalar
binomial coefficients needed in the finite unipotent expansion.

Induction on the lattice rank splits an integer tuple into its zeroth coordinate
and its tail. The published integer-power unipotent binomial formula expands the
zeroth-coordinate operator as a finite sum. The induction hypothesis bounds the
tail coefficients for the finitely many resulting vectors. Multiplying the two
bounds and summing their nonnegative constants gives degree `(d + 1)*r`.
No finite-dimensionality or topology on the vector space is used.

The rank-zero case uses the constant norm of `ell v`. The induction also covers
`r = 0`: the binomial expansion then has an empty index set, so all the relevant
coefficients vanish. The proof imports the published
`Langlands.integerUnipotentBinomial` and
`Langlands.complexBinomialCoefficientPolynomial`, and reuses the coordinate
splitting maps from `Langlands.IntegerLatticeExponentialPolynomial`.

This is an algebraic prerequisite. Applying it to actual Jacquet actions and
comparing lattice coordinates with the actual matrix height are separate steps
in the Xi upper-bound argument.
