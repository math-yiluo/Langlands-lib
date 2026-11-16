# Quotients by finite flat normal subgroups over affine bases

`Langlands.GroupScheme.finiteNormalSubgroupQuotient` constructs an actual
quotient group scheme and projection in every universe. Its inputs are an
affine scheme `S`, an affine group scheme `G` over `S`, a group scheme `N`
whose structure morphism is finite, flat and locally of finite presentation,
and a homomorphism `i : N ⟶ G`. The underlying morphism of `i` is assumed
monomorphic, and its full range subgroup functor is assumed normal on every
test over `S`.

The result has type `FiniteNormalSubgroupQuotient i`. Its fields supply an
actual group scheme `quotient`, a homomorphism `projection : G ⟶ quotient`,
affineness of the quotient over `S`, finiteness of the projection, and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) projection`. The last
condition means that the projection is flat, surjective and locally of finite
presentation, and that the range of its actual scheme kernel equals the
range of `i` as a subgroup functor on all tests. Surjectivity here is
surjectivity of the scheme morphism; it does not assert surjectivity on the
points of every test scheme.

This is an internal construction from published Library results. The
underlying affine quotient comes from
`FiniteLocallyFreeQuotient.existsAffineQuotient` in
`Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof`.
The group structure and exact full kernel come from the descent construction
in `Langlands.GroupScheme.NormalQuotientGroup`. No additional external source
claim is made.

The existence proof
`exists_affine_quotient_of_finite_flat_normal_subgroup` uses the actual right
coset relation `G ×_S N`, with source `(g,n) ↦ g` and target
`(g,n) ↦ g i(n)`, from `HomogeneousCosetRelation`. The submitted
`scheme_arrow_unique` lemma promotes joint monicity from tests over `S` to
arbitrary scheme tests by giving each test its induced map to `S`. The
`scheme_equivalence` lemma proves reflexivity, symmetry and transitivity on
arbitrary scheme tests using the full range subgroup's unit, inverse and
multiplication. Composable arrows induce the same map to `S`, so these
operations apply in a single group of points over `S`.

The source projection is finite, flat and locally of finite presentation by
base change from `N`. The published translation automorphism identifies the
target projection with the source after an isomorphism, giving it the same
properties. The affine equivalence relation theorem then supplies an affine
scheme `Y`, a finite flat surjective locally finitely presented map `p`,
the actual kernel-pair square, and the coequalizer property.

The structure map of `G` descends along that coequalizer to a map `Y ⟶ S`.
The kernel-pair square and the published coset criterion show, on every test
over `S`, that two points have equal images precisely when their right
difference lies in the range of `i`. Normality now allows
`NormalQuotient.groupScheme` to descend the group operations and
`NormalQuotient.hom` to equip `p` with its homomorphism structure.
`NormalQuotient.isFppfQuotient` supplies the exact full kernel assertion.
Affineness over `S` follows because both `Y` and `S` are affine.

The definition `finiteNormalSubgroupQuotient` uses classical choice on this
proved existence theorem to package the actual group, projection and all
properties. No smoothness, connectedness, field or reductivity assumption is
used. Applying this construction in the fibrewise isogeny argument still
requires constructing the finite flat normal part of the kernel and proving
reductivity of the resulting quotient.
