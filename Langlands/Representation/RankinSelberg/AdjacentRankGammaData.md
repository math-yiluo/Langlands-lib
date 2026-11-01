# Certified adjacent-image gamma products for an irreducible test

This is an internal composition of the existing equal-rank gamma construction,
the actual twisted-test matrix functional equation, and the separated adjacent
comparison. It is a prerequisite for the adjacent-rank gamma analytic base;
it does not prove the closed two-block gamma statement.

`AdjacentRankImageGammaFactorization` asserts the existence of two rational
functions with complete `IsPadicSymmetricGammaFactor` certificates for the
equal-rank pair `(σ, τ)` and the pair `(τ, rankOneCharacter χ)`, and a complete
certificate for their product for `(π, τ)`. The definition fixes the additive
character and the supplied scalar Haar measure. It retains independent field,
first block, test and ambient carrier universes.

`adjacentRankImage_gammaFactorization_of_irreducible_test` proves this assertion
when the block and ambient representations have full Whittaker type, the test
has full inverse-character Whittaker type and is irreducible, and the whole
actual adjacent model-map range equals the range of a specified nonzero ambient
functional. It also takes a specified nonzero block functional, a specified
nonzero test functional, self-duality of the supplied scalar measure, and a
compatible quotient measure with its invariant-measure instance. These remain
explicit hypotheses. In particular, the theorem does not construct the ambient
image realization or remove the test irreducibility restriction.

The proof proceeds as follows.

1. Convert the test functional from the scaled standard character to the inverse
   character without changing its underlying linear functional. The published
   equal-rank functional equation supplies fixed polynomials, a minus-one scalar,
   an epsilon unit, an integer exponent, and normalized equations for every
   equal-rank coefficient and row test. The full equal-rank gamma construction
   gives an existing certificate. The normalized generators convert the supplied
   epsilon equation to a gamma equation, and fixed-functional uniqueness
   identifies the certified gamma function with the fixed rational expression.
2. `exists_adjacentRankMatrixFunctionalEquationWitnesses` constructs actual
   normalized matrix data on the determinant-twisted test coefficient image,
   together with its literal matrix witnesses. Irreducibility makes the actual
   coefficient-model map an equivalence. Twist that equivalence and transport
   the full matrix data to the determinant twist of the original test.
3. The private helper `gammaData_rankOne_of_matrix` passes the coefficient-model
   map through the top subrepresentation. Its surjectivity and the published
   subquotient coefficient-inclusion theorem provide the actual matrix
   coefficient inclusion required by the ambient matrix comparison. This
   produces a complete trivial-test gamma certificate for the twisted test.
   `rankOneGammaTwist` turns it into the complete certificate for the original
   test against the specified rank-one character. Full Whittaker type of the
   twisted test follows from the published determinant-twist equivalence.
4. Full Whittaker type of the ambient representation and test constructs its
   existing unequal-rank gamma certificate. The separated comparison identifies
   its rational function with the expression having product polynomials,
   multiplied epsilon units and added exponents. This comparison uses the
   actual same-family matrix and equal-rank equations from the preceding steps.
   The dual product polynomial is nonzero by the supplied normalized-generator
   certificates.
5. Algebra in the rational-function field splits that product expression into
   the two certified expressions. The equal-rank and unequal-rank adapters
   retain the complete symmetric factor predicates, including their compatible
   measure witnesses, nonzero-functional witnesses and universal equations.

No unrestricted or finite-block JPSS multiplicativity theorem is used. The
normalization is the existing `rationalGammaExpression`: the epsilon monomial
multiplies the original polynomial and divides by the reflected dual polynomial.
The proof performs rational-function algebra only; it does not cancel a
polynomial on unrestricted bilateral coefficient series. Generic-socle passage
for arbitrary tests, actual large-twist image realization, continuation in the
second block, and ordered normalized-induction reversal remain separate steps.
