# Product L-polynomial data from reflection rigidity

`TemperedLFactorProduct.ProductLPolynomialData` records a certified
L-polynomial for the two actual canonical normalized inductions, certified
polynomials for every block pair, equality with their double product, and
nonvanishing throughout the open complex unit disk. The canonical field,
supplied character and self-dual Haar measure, both rank orders, and independent
field and block-carrier universes are retained.

`nonempty_productLPolynomialData` constructs these data assuming full
Whittaker type of each block, irreducibility and analytic square-integrability
of each block, and the explicit closed proposition
`SquareIntegrablePoleFreeStatement`. These are conditional construction
premises. This module does not prove that proposition, derive full Whittaker
type from square-integrability, or prove the closed `TemperedLFactorStatement`.

The construction obtains original certificates and a normalized polynomial
residual from `TemperedLFactorDivisibility.twoFamilyLPolynomialData`, and
actual inverse-transpose certificates and a dual residual from
`TemperedLFactorDual.nonempty_dualTwoFamilyLPolynomialData`. The gamma
comparison constructor supplies the identity between the original and
reflected dual ratios, up to an explicit Laurent monomial.

Inverse transpose preserves block irreducibility by the published surjective
pullback lemma. The published continuous-automorphism transport theorem
preserves the unchanged analytic square-integrability predicate. The supplied
pole premise therefore gives nonvanishing for every original and dual block
polynomial, using certificate uniqueness. For the dual blocks the negated
character uses `DominantRankTransport.negatedSelfDualHaar`, whose underlying
measure is the original supplied measure. Finite products preserve
nonvanishing.

Normalization makes the two induced polynomials nonzero; nonvanishing at zero
makes the dual block product nonzero. The algebraic cancellation lemma then
turns the gamma ratio into a reflected identity between the normalized
residuals. The reciprocal residue scale has norm less than one. Applying the
published reflection rigidity theorem through `eq_of_reflected_quotients`
shows that both residuals equal one, gives the original product equality,
and transfers nonvanishing to the induced polynomial.

This is a derived internal assembly of the named certified divisibility,
gamma, transport, pole-premise and reflection results. It introduces no new
original-literature assertion or analytic existence theorem.
