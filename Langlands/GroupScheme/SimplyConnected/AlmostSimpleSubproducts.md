# Actual subproducts of almost-simple factors

Worker 166. This internal construction builds actual finite subproducts and
their coordinate insertions and retractions. Membership in their all-test
subgroup ranges means that each omitted coordinate is the identity. The
coordinate criterion proves normality. An ordered list product of single
coordinates proves that a subgroup functor contains a subproduct precisely
when it contains every selected factor, including for noncommutative factors
and the empty subset.

For a supplied `SimplyConnectedAlmostSimpleProduct G`, `D.subproduct s` is the
actual product of the factors with indices in `s`. The maps
`D.subproductInclusion s` and `D.subproductProjection s` are homomorphisms to
and from the original group, and their composite on the subproduct is the
identity. If the original group is affine, this section is a closed immersion.
The coordinate criterion is transported through the supplied product
isomorphism to prove normality in the original group.

Each subproduct is smooth and geometrically connected, hence connected over
the ground field. To prove this for finite products, the implementation uses
the property that a structure morphism is both smooth and geometrically
connected. It is stable under composition because smooth morphisms are
universally open, under which hypothesis geometric connectedness composes.
The identity has the property, as its pullback to a field is isomorphic to that
field's spectrum. The published finite-product property theorem then applies.
Each factor supplies smoothness, affineness and connectedness through its
almost-simplicity, and the published connected-group theorem supplies its
geometric connectedness.

Finally, `D.range_subproductInclusion_le_iff` states the same factor-generation
criterion inside the original group, for an arbitrary all-test subgroup
functor there. Its proof applies the generic product criterion to the inverse
image of the subgroup under the product isomorphism.

All fields and schemes have arbitrary universe `u`. The subset may be empty
or the full index set. The construction derives from categorical finite
products, the published coordinate inclusions, and the published geometric
properties of the factors. It introduces no external structural premise.
It does not yet assert Galois invariance, transitivity, descent of a factor,
or the final Weil-restriction decomposition.
