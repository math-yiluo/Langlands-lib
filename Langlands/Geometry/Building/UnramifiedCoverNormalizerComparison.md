# Transport of the unramified simply connected normalizer bound

This internal comparison transfers the explicit proposition
`MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement` to the image of
`N(K) ∩ G(K)^♮` for any supplied ambient building and unramified zero datum.
It is conditional on that proposition and does not prove it.

The implemented proof uses the actual integer-valued derived-cover source building
constructed by `IntegerValuationBuildingData.derivedCoverSourceData`. Lift an
ambient normalizer point in the simply connected image to its source normalizer.
The assumed range equality places its source action in the source affine Weyl
group. Equivariance conjugates the original source action to the original ambient
action, and exact transport of affine roots conjugates the affine Weyl groups.
No apartment or root comparisons are additional hypotheses.

The generic action-conjugation lemma works over any field with an explicit
integer-valued valuation. The elementwise corollary is the form needed by the
zero-fixer reduction. These are derived internal helpers, with provenance in the
Library source-building construction and affine-root transport theorems; no
additional external mathematical source is used.

`simplyConnectedImageNormalizerWeylActionOfStatement` packages the restricted
original normalizer action as a group homomorphism to the affine Weyl subgroup.
Its coercion theorem records that the underlying action is exactly the supplied
normalizer action. It retains the unproved normalizer proposition as an explicit
argument.
