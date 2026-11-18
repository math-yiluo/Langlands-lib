# Finite-subset weight comparison for adjoint exterior powers

Given a split pinning, an embedding of root indices into an ambient index type,
and a finite set `O` of simple roots, `positiveRootComplementIndices` selects
the positive root indices outside `O`. The cardinality lemma gives the number of
positive roots minus `O.card`. If the ambient weights agree with the indexed
roots on the embedded indices, their sum over the selected subset is the
published positive-root sum minus the sum of `O`.

The comparison lemma also assumes that every index outside the embedding has
weight zero. The integral simple-root basis gives a linear form on the root
span with value one on `O` and two on the other simple roots. A positive root
has value at most one exactly when it belongs to `O`. Its expression in simple
roots is a nonzero sum with natural coefficients, and degree at most one forces
one coefficient equal to one on a root in `O` and all other coefficients zero.
Negative roots have nonpositive degree by applying this form to their opposites.
Consequently the selected indices have degree greater than one and all other
indices have degree at most one.

Any distinct subset of the same cardinality exchanges equally many indices
with the selected subset. The dropped indices each have larger degree than the
added ones, so the new subset has a strictly smaller degree sum. Every element
of the simple-root monoid has nonnegative degree. This proves that the new
weight minus the selected weight lies outside the monoid and rules out equality
of their weight sums. The comparison is derived from the integral root datum
and is independent of the characteristic of the field. It applies also to an
empty set of omitted roots and to an empty complementary subset.
