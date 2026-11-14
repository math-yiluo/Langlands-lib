# Actual root and full-centralizer open charts

This internal construction assembles ordered root products with a full
whole-torus centralizer into an actual open multiplication chart over a field.
The ambient group is smooth, connected and affine, the torus is split, and the
cocharacter is generic for its actual relative roots.

The negative and positive lists come with `DynamicRootProductData` and positive
pairings for the corresponding signed cocharacter. Full relative-root
representatives may be replaced freely: the factorization criterion on all
test schemes shows that their internal ordered products remain isomorphisms.
`rootProductIsoOfRepresentatives` records the resulting scheme isomorphism,
and its composite is exactly the ambient ordered multiplication.
The middle factor is a representative of the full torus centralizer. Genericity
identifies it with the dynamic centralizer. The three-block splitting theorem
and the dynamic open-cell theorem then make actual ordered multiplication an
open immersion. These statements include empty negative or positive lists.

The proof reuses the existing full-subgroup representative transport,
`OrderedIntegralOpenCell` three-block splitting and the dynamic triple cell.
It is an internal consequence of those interfaces, with no new literature
assertion. Compatible maps and full-kernel assembly will be added separately.
