# Relation laws for symmetric cross-correspondences

This internal helper supplies the relation laws in the symmetric tuple route
motivated by Stacks Lemma 68.8.3, Tag 0BBN, first proof paragraph. The source is
registered as `stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The actual quotient schemes come from the preceding helpers using the published
specialization of Stacks Proposition 39.23.9, Tag 03BM, registered as
`stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`,
`03BM.txt`, statement and proof. The present APIs are derived from the original
relation laws, the previously proved cartesian cross-endpoint square, and
Mathlib's effective epimorphism and lifting properties; the sources are not
claimed to state these exact APIs.

For an étale equivalence relation `E` with separated source map,
`tupleCrossUnit` constructs the arrow from an ordered distinct tuple to itself
using the identity arrow of `E`. Its two endpoint lemmas give identity maps.
`tupleCrossSwap` exchanges the two ordered tuple endpoints using the inverse
arrow of `E`. Its endpoint lemmas give the two original endpoints in reverse
order.

With `E.U` and `E.R` affine, `tupleCross_exists_of_symmetric` lifts a symmetric
cross arrow once ordered representatives for both endpoints are specified.
The cartesian joint endpoint square supplies the lift; projecting its first
factorization equation supplies the ordered endpoint equations.

The remaining declarations also assume that the original joint relation map
`prod.lift E.t E.s` is a closed immersion.
`tupleSymmetricCross_hom_ext` uses the descended joint monomorphism to prove
extensionality in the two symmetric endpoints.
`tupleSymmetricCross_exists_of_cover` descends existence of a cross arrow along
a strong epimorphism of test schemes. The local arrow and the pair of global
endpoints form a square against the joint monomorphism. The lifting property
of a strong epimorphism gives the global arrow and its endpoint equations.
Finite étale surjections are eligible covers because they are effective
epimorphisms in the fpqc topology.

`tupleSymmetricCrossUnit` applies this descent to the ordered identity arrow
and the ordered-to-symmetric quotient map. Its two endpoint lemmas prove
reflexivity. `tupleSymmetricCrossSwap` applies it to the ordered swap and the
cross quotient map. Its two endpoint lemmas prove symmetry, and
`tupleSymmetricCrossSwap_swap` proves involutivity by joint extensionality.

`tupleSymmetricCross_transitive` proves transitivity for arbitrary test schemes
and three possibly different tuple lengths. Pulling back the product of the
three finite étale quotient maps gives a finite étale surjective cover on
which all three symmetric endpoints have ordered representatives. The
cartesian cross-endpoint squares lift both given arrows to ordered cross
arrows with the same middle tuple. Composition in `E` then gives an ordered
cross arrow between the outer tuples. Its image in the symmetric cross scheme
descends along the cover by the strong epimorphism lifting argument. No choice
of a global permutation on the original test scheme is made.

The universe `u` is arbitrary. These declarations establish reflexivity,
symmetry and transitivity for the symmetric cross-correspondences. They do
not yet prove étaleness of the symmetric endpoint maps, the stratification,
or the Noetherian first-level statement.
