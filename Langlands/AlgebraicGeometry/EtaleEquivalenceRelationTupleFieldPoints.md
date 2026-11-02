# Field points of distinct tuples and maximal-tuple matching

This internal helper continues the distinct-tuple filtration in Stacks
Lemma 68.8.3, Tag 0BBN, second proof paragraph. The source is registered as
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The paragraph identifies the appropriate unordered tuple fiber over an exact
degree stratum as a singleton. Here a related field-point matching calculation
is derived directly from the preceding tuple schemes, clopen equality loci,
and saturated threshold opens. The helper does not assume that source
paragraph's algebraic-space construction or a stratum comparison theorem.
The symmetric quotient used at the end is the actual quotient constructed
by the preceding helpers from Stacks Proposition 39.23.9, Tag 03BM, registered
as `stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`,
`03BM.txt`, statement and proof.

Assume the source of an étale equivalence relation `E` is separated.
`range_subset_tupleDistinctOpen_iff_of_field` proves that a field-valued tuple
factors through the distinct open exactly when its coordinate morphisms are
pairwise distinct. One direction uses the previous injectivity theorem. For
the converse, if the image point were in an equality locus, the entire field
spectrum would map into that locus, because a field spectrum has one point.
The equality-locus factorization criterion would then force the two coordinate
morphisms to agree. Thus `tupleDistinctFieldLift` realizes any pairwise related
injective family of field-valued coordinates as a point of the distinct-tuple
scheme. Its projection theorem recovers every given coordinate.

`tupleField_coordinates_exhaust` considers an injective related family of
`n + 1` field-valued coordinates and one more coordinate related to all of them.
If the image of the first coordinate lies outside threshold `n + 1`, the new
coordinate must equal one in the original family. Otherwise appending it gives
an injective related family of `n + 2` coordinates. Its distinct-tuple lift
puts the original first image point in the next tuple-image open, hence in its
saturation, contradicting the hypothesis. This uses an arbitrary field,
without an algebraic-closure hypothesis or a geometric-cardinality assertion.

`tupleDistinct_exists_permutation` applies to two tuples over an arbitrary
nonempty test scheme, under the explicit hypothesis that every coordinate
of the second tuple equals a coordinate of the first as a morphism on the
whole test scheme. Choosing these matches gives an injective self-map of the
finite index set, because the second tuple has distinct coordinates. It is
therefore a permutation; tuple extensionality gives the reindexing equation.
The global matching hypothesis is essential: this declaration does not select
a global permutation from matches that exist only locally.

When the object and relation schemes are affine,
`tupleSymmetricMap_eq_of_coordinate_matching` applies permutation invariance
of the actual symmetric quotient to that reindexing equation.
`tupleCross_fieldPoint_symmetric_eq_of_not_threshold` considers a field-valued
ordered cross arrow between two tuples of length `n + 1`, whose first image
point lies outside the next threshold. Every coordinate of the second tuple
is related to every coordinate of the first. The exhaustion theorem matches
each of these coordinates with one in the first tuple. The permutation
argument then proves equality of the two unordered endpoint morphisms.

The universe `u` is arbitrary throughout. These are field-point matching
results; they do not assert equality of endpoint morphisms on arbitrary
nonreduced test schemes, prove an isomorphism on a degree stratum, establish
étaleness of symmetric endpoints, or prove the Noetherian first-level statement.
