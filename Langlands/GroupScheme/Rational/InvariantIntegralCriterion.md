# A universal-coordinate criterion for invariant integration

This internal construction uses the actual coordinate presentation of an affine
group scheme over an arbitrary field. `Lie.universalPoint` is the affine point
corresponding to the identity homomorphism of its coordinate algebra.
`coordinateCoproduct` is the coordinate map of actual multiplication: its first
point is the extension of `Lie.universalPoint` to the first tensor factor, and its
second point is the universal point in the second tensor factor.

`tensorMap_leftTranslation` proves that translation commutes with extension of
the coefficient algebra. It compares the images of the two tensor factors; on
the coordinate factor the assertion follows by applying the natural
point-coordinate equivalence to the translated universal point.
`leftTranslation_includeRight` then obtains translation by any actual affine
point by specializing the first factor of the coordinate coproduct.

`left_invariant_iff_coordinateCoproduct` identifies the full translation law of
`InvariantIntegral` with the single linear identity
`contract (coordinateCoproduct z) = algebraMap (linearForm z)` on every coordinate
function `z`. The forward implication tests the law on the universal coordinate
point. For the reverse implication, contraction is natural under the coordinate
map of the given point; linearity extends the result from coordinate functions
to all tensors. This proves the law over every commutative coefficient algebra,
including nonreduced ones, without changing the original base field or universe.

`InvariantIntegral.ofCoordinateCoproduct` packages this equivalence and the
normalization `linearForm 1 = 1` into an actual invariant integral. Existence of
such a functional remains an input. The construction has internal provenance:
it is a direct consequence of the published actual coordinate, tensor-map,
translation and contraction APIs, with no reductivity or characteristic-zero
assumption and no complete-reducibility or Levi theorem.
