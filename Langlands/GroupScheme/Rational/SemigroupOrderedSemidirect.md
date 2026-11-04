# Ordered semigroup products in an actual semidirect product

This internal assembly works over any field and universe. Smooth connected
affine groups `K` and `G` carry an actual inner action of `K` on `G`, and a
commuting action of a split torus `S` on `G`. The actual lifted external action
on `G ⋊ K` fixes `K`.

`precomp_iso` transports an exact all-test subgroup representative along a
group-scheme isomorphism of its source. A range witness is transported by the
isomorphism or its inverse, and monicity is preserved by composition.

For each given representative of a normal-factor semigroup,
`semigroupInnerActionFamily` restricts the actual inner action. Stability of
each semigroup under this action is an explicit premise. Its inclusion is
equivariant on every test scheme. For a semigroup containing zero,
`isRepresentedBy_semigroupInnerSemidirectMap` applies the exact semidirect
factor identification and the represented stable subgroup construction.
This step assumes the global `SemigroupIntersectionStatement`.

`semigroupOrderedSemidirect_of_factors` takes an ordered product of smooth
connected closed normal-factor representatives, with an isomorphism given
by their actual ordered multiplication. The original blocks satisfy exactly
cross-exclusion of each block from every other positive generated semigroup.
A chosen block contains zero. The theorem constructs the ambient
representatives by absorbing `K` into that chosen factor. Cross-exclusion
excludes zero from every other generated block. The global
`SemigroupFunctorialityStatement` identifies these other ambient factors
with the normal-factor images. Their representatives are the original
inclusions followed by the ambient normal inclusion.

All constructed inclusions are closed. The chosen source is the product
scheme of its original normal factor and `K`, up to the explicit chosen
isomorphism. Smoothness follows from smoothness of a binary product over
the field. Connectedness follows from geometric integrality of products
of smooth connected affine groups. The other sources retain their original
geometry up to the explicit unchanged-factor isomorphism. The existing
absorption theorem proves that their original ordered multiplication is a
scheme isomorphism in the same order.

`semigroupOrderedSemidirect_of_larger_support` starts instead from
`HasOrderedSemigroupProducts b`, an arbitrary larger partitioned support
containing zero, and inclusion of the normal action's support into it.
It restricts the blocks to the normal support without changing their
semigroup functors, obtains their representatives, selects the unique
zero-containing block, and applies the factor theorem. An empty family
cannot cover a support containing zero; no arbitrary index is chosen.

The provenance is internal, combining the exact semidirect factor identities,
represented actions, original ordered-product absorption, support restriction
and smooth connected product geometry. The original APIs retain both global
comparison statements. The local variants retain global functoriality and
the exact inverse-image equalities. Inner stability, the normal-factor
product property, the larger-support containment and membership of zero remain
explicit premises where used. This unit does not prove these premises,
produce a solvable decomposition, perform scalar descent, handle the
zero-absent case, or prove the host
`SemigroupOrderedProductStatement`.

The `of_comap` variants assume only the inverse-image equalities along the
normal inclusion, for the supplied lifted action and every additive
semigroup. In the zero-containing case, the acting range lies in the ambient
semigroup; the all-test semidirect reconstruction and the local equality then
identify the represented semigroup. The equality is proved pointwise, so the
stability proof does not require dependent transport. The factor-absorption and larger-support
proofs use only these equalities. The original theorem names and signatures
remain wrappers obtaining the equalities from the full intersection statement.
