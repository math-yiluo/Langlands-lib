# Proof of global coefficient growth from finite independent charts

The proof is internal and keeps all structural inputs in the statement.
For each chart, `positiveCharacterOnIndependentCocharacters` supplies an
actual character positive on its independent cocharacters.
`rationalUniformizerCoordinateHeight` bounds the residue cardinality to
the sum of the natural coordinates by a positive constant times a natural
power of the actual matrix norm.

The supplied simultaneous standard basis and admissibility give
`rationalUnrestrictedLatticeBound` for that chart. Taking all three
translating sets to be the identity singleton produces the required
untranslated coefficient estimate for every smooth functional and vector.
`rationalCompactLatticePolynomialBound_of_power_height` combines this
estimate and the coordinate height, yielding a polynomial estimate
uniform over the two supplied compact sets and the finite translate set.

Choose the resulting exponent and positive constant in each of the
finitely many charts. Their summed exponents dominate every chart
exponent; the sum of their constants plus one is positive and dominates
every chart constant. Since the actual matrix norm is at least one,
these give a common polynomial estimate on every chart. The supplied
cover identifies every rational point with one of these products.

All four universes remain independent. The argument handles empty
coordinate families without a separate case. An empty chart family
cannot satisfy the cover of the nonempty group, but the sum construction
needs no nonemptiness assumption. No finite-length premise or central
character is used. The proof constructs neither the supplied simultaneous
standard basis nor the global covering data.
