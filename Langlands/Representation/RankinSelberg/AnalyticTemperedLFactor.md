# Certified L-polynomials of analytically tempered actions

Author: Worker 111.

This internal adapter constructs
`Langlands.RankinSelberg.AnalyticTemperedLPolynomialData` for two original
irreducible analytically tempered positive-rank general linear actions. Its
constructor is `analyticTemperedLPolynomialData`. The supplied parameters are
a prime, a p-adic field with canonical topological data, a nontrivial continuous
unitary additive character, a self-dual additive Haar measure, and the two
original actions with irreducibility and analytic temperedness proofs.
The field and the two carrier universes are independent. Both rank orders
and rank one are included.

The data contains a complex polynomial, its existing full
`IsPadicSymmetricLPolynomial` certificate for the original actions, and
nonvanishing at every complex number of norm less than one. It also contains
the full `IsOfWhittakerType` predicate for each original action: admissibility,
finite generation over the group algebra, and a linear equivalence of the
entire standard Whittaker-functional space with the scalars.

The helper `analyticTemperedWhittakerType` first uses analytic temperedness
to obtain admissibility and bundle the original action as a smooth
representation. The published
`Classification.temperedBlockExhaustion` discharges the exhaustion premise of
`temperedSquareIntegrableBlockDecomposition`. That bridge supplies actual
irreducible analytically square-integrable blocks in `Type (max uF uV)`, their
unitarizability, a successor-size block shape, and an actual representation
equivalence from the original action to their canonical normalized upper
induction.

Each block has full Whittaker type by
`squareIntegrableWhittakerType_of_genericity`, with its genericity input
discharged by the published `Classification.squareIntegrableGenericity`.
`normalizedProductWhittakerType` gives full type of the actual normalized
induction. `IsOfWhittakerType.of_equiv` transports all three clauses back
through the inverse of the decomposition equivalence. No Whittaker
functional or finite generation premise is supplied by the caller.

For the polynomial construction, decompose both original actions, allowing
different carrier universes. Apply the closed `temperedLFactor` theorem to
these two square-integrable block families. Retain its induced polynomial,
full symmetric certificate and open-unit-disk nonvanishing.
`IsPadicSymmetricLPolynomial.congr_equiv` transports that certificate back
through the two actual inverse equivalences, without changing the polynomial.
This retains the original character, supplied self-dual measure, compatible
quotient-measure quantifiers, and normalized-generator conditions.
Classical choice selects this nonempty certified data.

The provenance is internal composition of the published proof APIs:
[tempered exhaustion](../Classification/TemperedBlockExhaustionProof.md),
[the block decomposition bridge](TemperedTwistSupercuspidalPoleClassification.md),
[full square-integrable Whittaker type](SquareIntegrableWhittakerTypeOfGenericityProof.md),
[intrinsic square-integrable genericity](../Classification/SquareIntegrableGenericityProof.md),
[normalized product Whittaker type](NormalizedProductWhittakerTypeProof.md),
[tempered L-factors](TemperedLFactorProof.md), and
[certificate transport](PadicPairFactors.md).
This adapter adds no external classification assertion. The analytic
predicates keep their full-center, all-Haar matrix-coefficient meanings.
It is a prerequisite within the standard-module L-factor task: it does not
assert the block product formula for nonzero real Langlands exponents.
