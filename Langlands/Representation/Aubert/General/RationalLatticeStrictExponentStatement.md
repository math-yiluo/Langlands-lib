# Strict normalized exponents on actual uniformizer rays

Author: Worker 19. This is a derived internal statement for the general
rational strict Jacquet criterion.

`RationalLatticeStrictExponentStatement` uses the actual rational-point
group at `pointTopology`, the literal simple-root labels, the actual standard
Levis and radicals, and the Haar-normalized Jacquet functors of
`RationalStrictJacquetSquareIntegrabilityStatement`. The field and
representation universes are independent, with the same saturated
representation carrier as that target. It assumes the displayed strict
normalized Jacquet exponent condition.

For any selected set `J` of simple roots and any actual cocharacter `x`
whose pairings vanish on `J`, are nonnegative on all simple roots, and are
positive on at least one simple root, the conclusion constructs a point in
the full center of the actual Levi. Its underlying ambient point is exactly
`uniformizerPowers i (.ofAdd x)`. Every full-center exponent of that Levi's
actual normalized Jacquet module has norm strictly below one at this point.
The same point works for every exponent.

The internal derivation uses the published centrality of uniformizer powers
orthogonal to `J`, obtaining its finite-root and standard-cocharacter inputs
from maximal splitness, reductivity, and the supplied standard-cocharacter
statement. Evaluating a character on a cocharacter gives the chosen
uniformizer raised to their integer pairing. Its valuation is at most one
for a nonnegative pairing and strictly below one for a positive pairing.
Thus the actual torus point satisfies the literal valuation predicate in
the strict exponent hypothesis, which gives the asserted bound.

No admissibility, irreducibility, or finite-length hypothesis is needed for
this implication. For empty simple-root labels there is no cocharacter
satisfying the positive-pairing premise; this statement supplies no
compactness result for that case. It also supplies no contraction basis,
Cartan coverage, coefficient estimate, volume comparison, or integrability
claim. Those remain separate obligations of the full criterion. This
internal derivation uses no classification, geometric lemma, adjointness,
character independence, or cuspidal support assertion.
