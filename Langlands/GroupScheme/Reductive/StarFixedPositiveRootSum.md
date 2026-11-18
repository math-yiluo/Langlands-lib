# The positive-root sum as a star-fixed weight

`GaloisPinningData.starFixedPositiveRootSum` equips the published
`IntegralWeylVector.positiveRootSum` of the supplied split pinning with
`GaloisPinningData.IsStarFixedWeight`. Its value is definitionally the published
sum. `starAction_positiveRootSum` gives the equality for each algebra
automorphism of the splitting field over the ground field.

The construction is derived from the Library definitions of the star action and
the positive-root sum. Each star automorphism preserves the simple roots. The
based root-datum positivity lemma then shows that the induced permutation of
root indices preserves the positive indices. The weight-lattice action is
linear and maps each indexed root to the root at its permuted index. Applying
that action to the sum and reindexing proves the fixedness equality. The result
uses the full star action for the given Galois pinning in every characteristic.
