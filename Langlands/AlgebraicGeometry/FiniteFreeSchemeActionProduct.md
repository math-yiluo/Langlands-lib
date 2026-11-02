# Products of finite free scheme actions and affine quotients

This internal helper is derived from the finite free action quotient and finite
extensivity of schemes. It supports the symmetric-tuple construction of Stacks
Lemma 68.8.3, Tag 0BBN, first proof paragraph. The registered source is
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The actual affine quotient input comes through the preceding specialization of
Stacks Proposition 39.23.9, Tag 03BM, registered source
`stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`,
`03BM.txt`, statement and proof. The present product calculation is derived,
rather than asserted as an additional statement from those sources.

`schemeMorphismProperty_prod_map` shows that any property of scheme morphisms
stable under composition and base change is stable under the product of two
morphisms. Factor the product into a change of its first coordinate and then
of its second coordinate. Each factor is a base change of the corresponding
original morphism; the second pullback is obtained by exchanging coordinates.

For free actions `A` of `G` on `X` and `B` of `H` on `Y`, `product` is the free
action of `G × H` on `X × Y`. Its automorphisms act independently on the factors.
The identity and multiplication laws are checked by the two projections.
Freeness follows by projecting an equality of acted morphisms from an arbitrary
nonempty test scheme and using freeness of both original actions. All groups
and schemes live in the same arbitrary universe `u`.

`productRelationLeft` and `productRelationRight` project the coproduct relation
of the product action to the two original coproduct relations. Their four
source and target equations are `productRelationLeft_target`,
`productRelationLeft_source`, `productRelationRight_target` and
`productRelationRight_source`. The equations follow summand by summand.
When both groups are finite, `productRelation_isPullback` states that these
maps identify the product-action relation with the product of the two action
relations. The proof applies universality of finite coproducts in schemes to
the product square on each pair of summands, viewing products as pullbacks over
the terminal scheme. It does not select a single group label on a disconnected
test scheme.

For actual affine quotients `Q` and `Q'`, `productQuotient_isPullback` proves
that the product-action relation is the kernel pair of `prod.map Q.map Q'.map`.
An equality of the two product quotient morphisms gives one equality in each
coordinate. The two original kernel pairs lift these equalities to action
relation morphisms, and the preceding product pullback combines them. Uniqueness
uses the same two kernel-pair universal properties.

`productQuotient` packages `Q.scheme × Q'.scheme` and the product quotient map
as an actual affine quotient of the product action. Affineness follows from
the product of affine schemes. Finiteness, étaleness and surjectivity of the map
follow from the proved stability of morphism properties under products.
Its kernel pair is the preceding theorem, and its coequalizer follows from
Mathlib's effective epimorphism theorem for faithfully flat quasi-compact
surjective scheme morphisms. No new quotient existence assumption is used.
This helper makes no assertion about cross-tuple strata or Noetherian
approximation.
