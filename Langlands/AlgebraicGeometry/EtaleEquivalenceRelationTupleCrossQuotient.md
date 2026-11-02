# Affine correspondences between symmetric tuple quotients

This internal construction continues the symmetric-tuple step of Stacks
Lemma 68.8.3 (Tag 0BBN). The registered source is
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`,
`0BBN.html`, first proof paragraph. It constructs an affine correspondence
between two unordered-tuple schemes from their ordered correspondence.
It does not yet prove the descended correspondence is an étale relation or
an algebraic-space fibre product. The relation source is separated, all
schemes have universe `u`, and indices `m` and `n` mean `m + 1` and `n + 1`
coordinates.

`tupleCrossScheme` is the iterated pullback of the two distinct-tuple schemes
along the original relation. Thus its zeroth coordinates are related, and
all coordinates of both tuples are in the same relation class. Distinctness
is required within each tuple; coordinates in different tuples may agree.
`tupleCrossLeft`, `tupleCrossRight` and `tupleCrossMap` are the two tuple
projections and the original relation arrow. `tupleCrossMap_t` and
`tupleCrossMap_s` give its endpoints. `tupleCrossLift` realizes two tuples
and a compatible original arrow, with its three projection equations.
`tupleCross_hom_ext` proves that the two tuples alone determine a map to this
scheme: monicity of the original relation first determines the original
arrow, and then the two pullback universal properties give equality.
Both tuple projections are étale by base change and composition. When the
object and relation schemes are affine, the ordered correspondence is affine.

`tupleCrossCoordinates_related` composes the relation arrow from a chosen
left coordinate to the left zeroth coordinate, the original arrow, and
the arrow from the right zeroth coordinate to a chosen right coordinate.
It therefore supplies the relation arrow between any two cross-coordinates.
`tupleCrossReindex` uses this witness and the pullback lift to permute both
tuples independently. Its left and right projection equations are
`tupleCrossReindex_left` and `tupleCrossReindex_right`.
`tupleCrossReindexIso` uses the inverse permutations as inverse morphism;
the inverse identities follow by comparing both tuples and all coordinates.
`tupleCrossPermutationAction` packages the product of the two lifted
symmetric groups as a free action. Identity and multiplication follow by
the same coordinate comparisons. Freeness follows by projecting to each
tuple and applying freeness of its permutation action on a nonempty test
scheme.

Under affineness of the object and relation schemes, `tupleCrossQuotient`
applies the generic finite free action quotient. The scheme and map are named
`tupleSymmetricCrossScheme` and `tupleSymmetricCrossMap`. Instances record
affineness of the scheme and finiteness, étaleness and surjectivity of that
map. The composites of the two ordered projections with their symmetric
quotient maps are invariant under the product action.
`tupleSymmetricCrossLeft` and `tupleSymmetricCrossRight` descend these
composites to the affine correspondence; the two
`tupleSymmetricCrossMap_left` and `tupleSymmetricCrossMap_right` equations
describe the factorization.

The quotient existence input is the preceding generic construction based on
the published proof of Stacks Proposition 39.23.9 (Tag 03BM), registered
source `stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`,
`03BM.txt`, statement and proof. The present module derives the ordered
correspondence and action directly from the existing equivalence relation
and tuple constructions. It does not assume a quotient algebraic space,
a stratification, or a Noetherian approximation statement.
