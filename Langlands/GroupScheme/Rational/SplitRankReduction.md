# Split rank from maximal extension and source isomorphisms

Worker 1271. The internal definition `IsSplitTorus.rank` chooses a finite
splitting of an actual split torus and takes its number of factors.
`IsSplitTorus.rank_eq_card` proves that every other finite splitting has
that same number, by the integral cocharacter isomorphism rank comparison.
Thus the definition is independent of the chosen splitting.

This reduction also proves that the published supremum
`splitRank` of a finite split torus is its number of factors. Every term in
the supremum is bounded by the integral cocharacter rank comparison, and
the identity map supplies the reverse inequality. Ambient isomorphism
invariance gives the same formula for every specified split presentation.

A closed split torus factoring through a split group has rank at most that
of the intermediate split group. The proof uses monomorphism cancellation:
the composite is a closed immersion, so the first factor is a monomorphism
on schemes over the field. It then transports to split coordinates and
applies the integral cocharacter rank bound. The first factor need not be
assumed closed.

For a fixed maximal split torus, the rank equality is proved under two
explicit hypotheses. Every closed split torus must extend through a
maximal split torus, and the source of every such maximal torus must be
isomorphic to the fixed source. Given these hypotheses, each term of the
supremum is bounded by the fixed rank. The published lower bound supplies
the opposite inequality. Rational subgroup conjugacy supplies the required
source isomorphisms.

The final theorem assembles these hypotheses into the exact arbitrary
universe proposition `MaximalSplitTorusConjugacyStatement`. It remains a
conditional reduction: neither maximal extension nor reductive-group
rational conjugacy is proved here. In particular it is not a proof of the
host task's unconditional target.

The provenance is internal, using the published split-rank construction,
the integral cocharacter comparison, and the subgroup-conjugacy interface.
