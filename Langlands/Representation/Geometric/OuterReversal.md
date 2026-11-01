# Outer reversal of actual block refinements

This internal coordinate construction reindexes the outer blocks of a product
Levi. It is derived from the published definitions of block reversal, product
subgroups, refined projections and moduli. It retains each inner ordered shape.
It makes no assertion of the full Aubert compatibility theorem.

`outerReverseRefinement B` is an equivalence from refinements of `B` to
refinements of `B.reverse`; its forward formula is `S ↦ (i ↦ S i.rev)`.
Dependent function reindexing supplies the inverse, including its required
size transports. `refinementSignExponent_outerReverse` proves that the exact
product-Levi Aubert sign exponent is unchanged, by reindexing the finite sum.

`OppositeCuspidalJacquetFiltration.leviReverseEquiv (R := F) B` acts on the actual coarse product Levi by
`m ↦ (i ↦ m i.rev)`. The inverse evaluation formula is stated at indices in the
image of reversal, which avoids suppressing dependent size transports.
Membership in the refined upper parabolic and refined diagonal Levi is
preserved in both directions. Restriction therefore gives actual multiplicative
equivalences on those two subgroups. `refinedLeviProjection_outerReverse`
identifies their actual diagonal projections; it is a definitional equality
because the outer relabelling preserves all inner coordinates.

The existing `OppositeCuspidalJacquetFiltration.reverseMatrix_mul_leviEmbedding`
identifies this coarse reindexing with actual conjugation by `B.reverseMatrix`:
the embedded reversed element is sent to the embedded original element. The
coarse reindexing and conjugation identity are reused from
[`CoarseLeviReversal`](CoarseLeviReversal.md), which contains their unchanged
published declarations extracted from the classification transfer proof.
This shared coordinate module has no classification-theorem dependency.

All three equivalences are bicontinuous for the actual product and subgroup
topologies, without an assumption on continuity of multiplication in the
coefficient ring. For a supplied p-adic field and topology,
`refinedLeviModulus_outerReverse` proves invariance of the full explicit
positive modulus by reindexing its factors. The canonical positive complex
half modulus is therefore unchanged as well. Combining this with the projection
identity proves `refinedParabolicHalfModulus_outerReverse`, the equality needed
for actual normalized-induction covariance.

The ring and field universes are arbitrary. Every coordinate construction and
identity includes rank zero and its empty product. No admissibility,
irreducibility, finite vector-space dimension, classification conclusion or
additional preservation premise is used.
