# Products of exponent characters and coordinate permutations

For a scheme `S` and finite coordinate types, `splitTorus.characterProjection`
is the product of any supplied family of actual exponent characters. On every
test scheme its coordinates are the prescribed integral monomials.
`characterProjection_eq_exponentTorusProjection` identifies it over an affine
base with the published arbitrary-ring monomial projection.

`coordinatePermutationIso S e`, for `e : J ≃ I`, is the actual group-scheme isomorphism
from the split torus indexed by `I` to that indexed by `J` whose target
coordinate `j` is source coordinate `e j`. The module proves this formula,
the identity law and the contravariant composition law. The name distinguishes
this target-to-source indexing convention from the published
`splitTorus.reindexIso`, which accepts the inverse equivalence.

If an actual torus map transports characters by a supplied integral linear
map and takes one chosen exponent family to another through `e`, then
`characterProjection_comp_reindex` proves the square with `coordinatePermutationIso S e`.
`characterProjection_baseChange` proves compatibility with every base
change using the canonical split-torus identifications.

This is an internal derived construction from products, the published exponent
characters, their all-test evaluation formula, and the canonical split-torus
base-change point formula. Products define the maps; product uniqueness
proves the permutation laws, and the natural point equivalences prove the
remaining identities. No descent or splitting existence is asserted.
