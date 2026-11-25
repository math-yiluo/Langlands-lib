# Intrinsic weights for actual affine group homomorphisms

This derived module connects intrinsic weight-subgroup functoriality to actual
group schemes over an arbitrary commutative base ring. The source and target
have supplied affine scheme presentations, with no restriction on their
coordinate algebras. Actions are split-torus actions on their actual coefficient-
point functors, natural over every base algebra.

`affinePointsTransformation` is the actual natural group map induced by an actual
group-scheme homomorphism. `toModel_map` proves that this map and the explicit
corepresented model map form a commuting square with the actual affine-model
comparison homomorphisms. Its proof reads the universal affine point in the
source presentation and uses the published affine point comparison; the charts
need not respect addition.

`AffineCorepresentation.intrinsicWeightSubgroup` pulls the represented intrinsic
weight subgroup back to the actual affine group. For every additive semigroup
of characters, `map_mem_intrinsicWeightSubgroup` proves that an actual group map
which is equivariant on every coefficient algebra preserves this subgroup on
EVERY scheme test. The test scheme need not be affine or reduced.

`mem_intrinsicWeightSubgroup_iso_iff` proves membership equivalence for an actual
group isomorphism with forward equivariance. Equivariance of its inverse is
derived from the induced actual coefficient-point natural isomorphism.
`intrinsicWeightSubgroup_independent` then proves equality for two different
affine presentations of the same actual group and coefficient-point action.

This supplies actual-map and affine-presentation independence. It does not
construct the ambient conjugators, prove their compatibility with canonical
face-cocharacter actions, or supply parabolic normalization,
change-of-torus and effective descent data.

`affinePointsTransformation` abbreviates the existing
`Chevalley.affineMapNat`, whose affine-test natural transformation has the
same defining expression.
