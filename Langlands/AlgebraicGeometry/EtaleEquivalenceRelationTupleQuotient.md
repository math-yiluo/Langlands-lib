# Affine symmetric quotients of distinct related tuples

This derived helper constructs the symmetric quotient in the first proof
paragraph of Stacks Lemma 68.8.3 (Tag 0BBN), for an étale equivalence relation
whose object and relation schemes are affine. The registered original is
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`,
`0BBN.html`, statement and proof. Index `n` means `n + 1` coordinates, so the
scheme constructed here corresponds to the source's `V_{n+1}`. All schemes
have arbitrary universe `u`.

`TuplePermutationGroup` lifts the finite symmetric group to universe `u`, as
required by the generic scheme-action interface. `tuplePermutationAction`
acts on the actual distinct-tuple scheme using its coordinate reindexing
isomorphisms. Identity and multiplication are verified by comparing every
coordinate. With the convention used by the action interface, the composite
of the morphisms for `g` and `h` is the morphism for `g * h`: its coordinate
`i` is the original coordinate `g(h(i))`. Freeness on every nonempty
scheme-valued family follows from injectivity of the coordinate morphisms of
a distinct tuple. Equal action composites therefore give equality of each
permutation coordinate, hence equality of the lifted permutations.
`tuplePermutationAction_projection` records the coordinate equation.
These constructions require the relation source map to be separated.

When both schemes of the relation are affine, the distinct-tuple scheme is
affine. `tupleSymmetricQuotient` applies the preceding generic finite free
action quotient construction. `tupleSymmetricScheme` and
`tupleSymmetricMap` name its actual scheme and quotient morphism.
The four instances record that the target is affine and the morphism is
finite, étale and surjective. `tupleSymmetricMap_invariant` gives invariance
under coordinate permutations. `tupleSymmetricMap_isPullback` identifies
the disjoint union of permutation graphs with the kernel pair of the
quotient map. `tupleSymmetricMap_isColimit` records its coequalizer
property. `tupleSymmetricDesc`, `tupleSymmetricMap_desc` and
`tupleSymmetric_hom_ext` give descent, its factorization equation and
uniqueness for a permutation-invariant morphism.

The generic quotient helper derives its existence from the published proof
of Stacks Proposition 39.23.9 (Tag 03BM), registered original
`stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`.
This module specializes that construction and the preceding distinct-tuple
reindexing lemmas. It does not yet construct cross-relations between these
quotients, their open filtration, or a Noetherian first level.
