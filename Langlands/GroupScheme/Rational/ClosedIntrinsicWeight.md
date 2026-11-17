# Closed equivariant inclusions reflect intrinsic weight subgroups

Work over any commutative base ring, with group functors corepresented by arbitrary commutative algebras and split-torus actions. No field, finite-type, reducedness, or smoothness condition is imposed.

An equivariant natural group map induces a coordinate pullback that commutes with every homogeneous component (`comp_transformationPullback`). The proof compares the universal twisted points using equivariance and naturality, then reads coefficients of the resulting Laurent-algebra equality. If this pullback is surjective, membership in every intrinsic weight subgroup is reflected as well as preserved. Each source function has a target lift, and component compatibility transfers exactly the defining augmentation equations. The comparison also holds on every scheme test of the actual corepresented models.

For actual affine group schemes equipped with arbitrary affine presentations, `transformationPullback_surjective_of_isClosedSubgroup` proves the required surjectivity from a closed immersion of the actual groups. The induced map of models is the original map conjugated by the two affine charts; its map on global sections is surjective. Naturality of the canonical spectrum section isomorphisms then gives surjectivity of the actual algebra pullback.

`intrinsicWeightPreimage` is the actual subgroup functor obtained by pulling the target intrinsic subgroup back along an actual group homomorphism. `intrinsicWeightPreimage_eq_of_isClosedSubgroup` identifies it with the source intrinsic subgroup whenever the closed inclusion is equivariant over every coefficient algebra. Equality is proved on every scheme test; the coordinate charts need not respect addition.

Provenance: internal extension of intrinsic weight functoriality, using homogeneous components, the closed-immersion surjectivity theorem for affine schemes, and the actual affine-model comparison. The result does not construct a stable closed subgroup or a relative filtration.
