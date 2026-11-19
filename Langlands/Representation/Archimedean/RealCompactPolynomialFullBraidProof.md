# Laurent extension for the full compact braid

This file constructs an extension in which the compact polynomial factors
can be cancelled. For Laurent polynomials with coefficients in an
associative ring, the coefficient at the sum of two upper bounds on support
is the product of the two coefficients at those bounds. This follows from
uniqueness of a pair of supported exponents adding to the sum. An invertible
coefficient at an upper bound therefore gives left and right cancellation,
as can be seen using the maximum exponent of any nonzero difference.

For an input complex algebra \(A\), the construction uses Laurent
polynomials with coefficients in the complex-linear endomorphisms of
bilateral sequences in \(A\). The raising operator shifts indices, the
lowering operator shifts in the other direction and multiplies the result
at index \(n\) by \(-(n+1)n\), and the weight operator multiplies it by \(2n\).
They satisfy the three \(\mathfrak{sl}_2\) commutators and commute with
coordinatewise left multiplication by \(A\). Multiplication by the central
Laurent monomials of exponents \(1,-1,0\) retains their commutator relations.

The proof adds \((E-F)/2\), \(i(E+F)/2\) and \(iH/2\) to the constant
operators for \(X,Y,Z\), respectively. These additions commute with the
constant operators and satisfy the same three commutators. The lifted first
and second generators have support bounded above by one. Their coefficients
at one are nonzero complex multiples of the bilateral shift, hence units.
The central-factorial recurrence propagates this property to every factor
of either generator. It gives support bounded above by the factor index
and the corresponding power of the generator's coefficient at one.

The proof inducts strongly on the first index with the input algebra and
triple universally quantified. For each smaller index, it applies the
induction hypothesis in the Laurent extension, exchanging the two
generators and negating the third. Rewriting with the two corner
factorizations gives equality after multiplication on each side by a
regular factor. Cancellation gives the smaller-index evaluations needed
by `RealCompactPolynomialCornerInterpolation.normal_eq_of_small`. The
resulting corner equality yields the full identity in the extension.

Finally, the augmentation evaluates the Laurent variable at one. Both
lifted generators then preserve the sequences in \(A\) that vanish at all
negative indices. The index-zero values of the unscaled shift and lowering
operators on that subspace are zero. The augmented generators therefore
act by left multiplication by \(X\) and \(Y\) on the index-zero quotient.
The proof transports this action through the central-factorial recurrence
and both triple products. Applying the resulting operator equality to
the sequence supported at zero with value one gives the identity in \(A\).
