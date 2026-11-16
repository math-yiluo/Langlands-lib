# Pairing loci needed by the standard root-subset group proof

This internal helper derives the weak and zero pairing descriptions of the standard parabolic and Levi root subsets in either allowed ambient root set. Its inputs are a published relative-root-system realization, a split torus, a generic cocharacter, a subset Θ of the actual simple relative roots, and a standard cocharacter ζ for Θ. It is intended to supply only the root-set identities used by the group proof; it makes no convexity or root-triple classification claim.

The published comparison of actual simple roots with the indecomposable indivisible positive roots identifies the indecomposables in either ambient set. Strong induction on the positive integer pairing with the generic cocharacter therefore proves a positive-root induction principle whose addition step retains ambient membership of the sum. This is a direct derivation from the published comparison and the actual simple-root definition.

For any closed ambient subset containing both signs of Θ, simultaneous induction shows that each positive root of zero ζ-pairing and its negative lie in that subset. The summands have nonnegative ζ-pairing by the published standard-cocharacter sign lemma, so their pairings must vanish when the sum's pairing vanishes. Genericity extends the result to all roots. Root-closure minimality gives the converse inclusion in the Levi case, since the zero locus is closed and contains both signs of Θ.

The weak pairing locus is closed and contains the parabolic generators: all roots positive for the generic cocharacter and the negatives of Θ. Conversely, a root with nonnegative ζ-pairing is either positive for the generic cocharacter, hence a generator, or negative. In the latter case the positive-root sign lemma applied to its negative forces zero ζ-pairing, placing it in the Levi root subset, which is contained in the parabolic subset.

All content is an internal deduction from published imports and the companion Weyl helper's root-closure lemma. This supplies the group proof without assuming an unpublished sibling proof of the full standard root-triple statement.
