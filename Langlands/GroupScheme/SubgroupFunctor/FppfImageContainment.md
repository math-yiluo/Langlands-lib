# Containment of full inverse images using fppf subgroup images

This is an internal generalization of the published
`SubgroupFunctor.IsFppfImage.comap_eq_of_kernel_le` proof.
`IsFppfImage.comap_le_range` assumes an actual fppf image of a represented
subgroup `F` under `q`, and a monomorphic subgroup inclusion `i` containing
both `F` and the full actual kernel of `q`. It concludes that the full inverse
image of the fppf image is contained in the range of `i`, on all test schemes.
The base scheme is arbitrary. Closedness and smoothness are not needed.

For a point in the inverse image, pull back the fppf map between the image
representatives. On this fppf cover it has a lift in `F`. The quotient of the
original point by that lift is in the kernel, so both factors and their
product lie in the range of `i` on the cover. The published monomorphic range
descent lemma gives membership on the original test scheme.

`IsFppfImage.comapRangeInclusion` packages this containment as a canonical group
homomorphism on each test scheme. Its value theorem states that the underlying
ambient point is unchanged.

The provenance is derived from the imported fppf-image witness and represented
subgroup descent. It does not assume that all test-scheme points lift through
an fppf surjection over the original test scheme.
