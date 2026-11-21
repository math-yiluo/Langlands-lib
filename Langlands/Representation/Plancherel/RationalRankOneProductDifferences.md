# Pointwise products and rational multiplicative differences

Let `H` be a connected reductive group over a nonarchimedean local field, with its actual unramified parameter group and rational scalar field. `HasDenseRankOneProduct` provides a presentation whose numerator and denominator are nonzero at every point of a common dense open set in the complex unramified character group. On that set the quotient agrees with a pointwise product of a complex unit and an ordered list of functions. Each function is assigned one valuation-lattice chart with first block of rank at most one. It is invariant under the complementary scalings of that chart whenever both parameters belong to the set.

To take a multiplicative difference, intersect the set with its preimage under the chosen translation. The quotient and complex unit are nonzero there, so every factor is nonzero at both points. Divide the product identities and cancel the corresponding invariant factor. Commutativity of the translations preserves the remaining local invariance conditions. The new numerator and denominator are the products given by `fractionMultiplicativeDifference_div`. For a nonempty chart list the terminal fraction equals one on a dense open set, and continuity of the regular numerator and denominator gives equality in the rational function field. For an empty list the original fraction equals the embedded constant.

For a nonzero fraction satisfying this product condition, `unitaryRegular_of_denseRankOneProduct` uses a uniform norm bound on regular values on a dense subset of the actual unitary unramified character group. The rank-one difference criterion gives algebraic regularity at every unitary point, and the empty-list case follows directly from regularity of constants.

`RankOneScalarPolePresentation.ofDenseRankOneProduct` constructs the
denominator needed when a scalar fraction is part of a whole-operator
product. It uses the multiplicative differences to identify the prime
factors of a reduced denominator with basis-coordinate roots. Roots on the
unit circle supply pole factors with their multiplicities. All other roots
and the unit relating the prime product to the reduced denominator go into
the remainder, which is nonzero at every unitary point. For an empty chart
list the constant fraction has denominator one. The original and new
fractions agree by a global identity after cross multiplication.

This algebraic construction implements the pole support used in the
regularity argument of Waldspurger (2003), V.2.3 and V.3.1, printed
pp. 294–295. The factorization needs the dense rank-one product identity.
The norm estimate used for cancellation can then concern the entire
operator product, including this scalar.
