# Left multiplication preserving the sharp chamber normalizer cover

The internal subgroup `sharpChamberCoverStabilizer C` consists of actual rational
points whose left multiplication and inverse left multiplication preserve
`sharpChamberNormalizerCover C`. The sharp fixer of `C` and the actual setwise
chamber normalizer lie in it, by subgroup multiplication and conjugation covariance.

For a supplied lift of a simple wall reflection whose Weyl action negates the
wall derivative, chamber exchange writes a left sharp factor as a reflected
sharp factor, a wall root factor and a chamber normalizer. Reflection moves the
first factor to the original sharp fixer. The rank-one multiplication lemma
handles the remaining reflection, wall factor and normalizer. A final right
sharp factor can be absorbed. All structural hypotheses are explicit.

This is an internal combination of generic chamber exchange, rank-one
multiplication and actual normalizer covariance in the original group.

The square of a simple lift acts trivially on the apartment, hence stabilizes
`C`. Its inverse multiplication therefore preserves the cover too. This puts
the lift in `sharpChamberCoverStabilizer C`.

Assuming each chamber-simple reflection has such an actual lift, generation
puts the entire affine Weyl group in the image of the normalizer part of this
stabilizer. Given any actual normalizer point `n`, chamber transitivity supplies
an affine Weyl element taking `C` to `n C`. Lift it to a cover-preserving point
`m`; the difference `m` inverse times `n` stabilizes `C`, hence preserves the
cover. Thus the entire actual normalizer lies in the cover stabilizer. This
last lemma keeps the actual simple-lift existence premise explicit.
