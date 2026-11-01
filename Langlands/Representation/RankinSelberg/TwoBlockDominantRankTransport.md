# Dominant-rank induction and certificate transport

Author: Worker 484.

This internal helper transports certificates for the dominant-rank gamma and
L proof. It proves no analytic factor comparison or closed dominant-rank target.

`reverseSum` reindexes the rank sum by the involution `Fin.revPerm`.
`lowerReversedToUpperEquiv` applies the published theorem
`Langlands.glOppositeProductReversal` to the reversed sizes, carriers and
representations. The double reversal is identified with the identity permutation
as a whole, so that dependent carriers and representations move with their block
sizes. The source is the actual lower normalized induction and the target is
the original canonical upper normalized block product.

`lowerReversed` packages that actual lower representation. `gammaConclusion`
and `lConclusion` require supplied full symmetric certificates for its induced
pair and for each reversed block pair. They reindex the block factors by the
same involution and apply the public symmetric-certificate equivalence theorem
to the actual representation equivalence. All measure and functional
quantifiers and existence witnesses inside those predicates are preserved.
The L conclusion retains exactly `X ^ e * (∏ i, Pi i) = Q * P`, with the
same `Q` and `e`. No rank inequality is needed for this transport.

The implemented argument is a derived application of the public normalized
induction comparison, rather than an assertion that commuting factor products
identifies induced representations. The underlying Section 4 analytic gamma
and L conclusions remain missing. They must eventually supply the lower
certificates before this transport can contribute to either final theorem.
No new assertion from JPSS is claimed here.

`LowerGammaDominantInput` and `LowerLDominantInput` expose the remaining
analytic obligations as proposition definitions for the actual lower
induction. Their quantifiers and hypotheses are those of the existing dominant
targets, including all three independent universes and exactly `t ≤ r`.
Neither proposition has been proved. `gammaDominant_of_lower` and
`lDominant_of_lower` show that those respective inputs imply the exact existing
upper-induction target definitions. They apply the lower input to the reversed
dependent family and obtain smoothness for the actual induction equivalence
from the given full Whittaker type. These are conditional reductions, not proofs
of either closed target.

`block_lt_of_dominant` expands the rank sum for the two positive blocks. Each
block index is strictly smaller than the test index, including the boundary
`t = r`. This derived arithmetic fact allows unequal-rank block analytic
theorems to be used without excluding the equal-rank induced pair. It does not
prove an analytic statement.
