# Actual Lie kernels of scheme-theoretic subgroup intersections

This module is internal, derived infrastructure. Its inputs are the published
scheme-theoretic pullback `subgroupIntersection` and postcomposition on actual
dual-number identity kernels in `Lie.KernelTargetMaps`. It introduces no new
literature assertion.

`Lie.kernelIntersectionLift` constructs the unique tangent point in the
intersection from tangent points of its two factors with the same ambient
image. The underlying dual-number point is the lift through the actual
pullback of schemes over the base. Its reduction is the identity because its
projections reduce to the identities in both factors; the pullback uniqueness
property detects equality after these two projections.

The projection theorems and `Lie.kernelIntersectionLift_unique` express the
universal property on the actual kernels. The theorem
`Lie.lieImage_subgroupIntersection_iff` then says that an ambient tangent vector
is in the image of the intersection exactly when this same vector is in both
factor images. The two witnesses on the right are required to map to the same
specified ambient vector.

All results hold over any commutative coefficient ring and any base
`Spec R`, at universe `u`. No affineness, smoothness, finite type, or
monomorphism hypothesis is used. When the two maps present closed subgroups,
the pullback is their scheme-theoretic subgroup intersection by
`GroupScheme.SubgroupIntersection`. The same construction still works for
arbitrary group homomorphisms.

For the rank-one solvable obstruction this interface allows a root vector in
the Lie-images of both a Borel and a rank-one centralizer to be carried into
their intersection. It makes no assertion about smoothness of that
intersection or the number of Borels of the rank-one centralizer.
