# Ordered positive products and the actual contracting group

This is an internal construction over an arbitrary commutative ring `R`, in
arbitrary universe `u`. It supplies an isomorphism of schemes over `Spec R`
from positive-root coordinate affine space to any affine group scheme
representing the actual contracting subgroup.

The structural motivation is Conrad, *Reductive group schemes* (2014),
Theorem 5.1.13, pp.143–145: ordered multiplication of the positive root groups
identifies their product with the dynamically constructed unipotent group.
The implementation here is derived from the Library's big-cell and dynamic
interfaces and the coordinate reconstruction in
`Reductive/SplitBorelPositiveCoordinates.lean`. It assumes supplied root maps
and a supplied big-cell open immersion; it does not construct those data from
reductivity and root-space freeness.

Let `i` map a finite coordinate split torus into a group scheme `G`, and let `u`
be actual additive-group morphisms into `G` equivariant for the characters `ch`.
For a cocharacter `ν`, `orderedProduct_mem_unipotent` proves that any finite
ordered list of these root maps with strictly positive pairings with `ν`
belongs to `Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)` on every
test scheme. The extension over the affine line scales coordinate `c k` by
`t ^ d k`, where the positive integer `d k` is its pairing. Equivariance gives
the required orbit on the punctured line, and positivity gives the identity at
zero. No affine hypothesis on the test scheme is used here.

`positiveProductMap` is ordered multiplication from the underlying scheme of
`VectorGroup.groupScheme R n`. `comp_positiveProductMap` gives its coordinate
formula after every test morphism. If the big-cell map for the supplied
negative and positive lists is an open immersion, positive-product uniqueness
proves that this map is a monomorphism.

Assume every negative pairing is strictly negative. The arbitrary-ring
reconstruction theorem transports along an affine scheme's canonical
`Spec Γ` isomorphism in
`exists_orderedProduct_eq_of_mem_unipotent_of_affine`. Thus every contracting
point on an affine test scheme is an ordered positive product.

Now let `j : U ⟶ G` represent the actual contracting subgroup, with `U` affine.
Here representation includes monicity and equality of subgroup functors on
all test schemes. Positive-product contraction gives a lift
`positiveProductToUnipotent` through `j`. Applying reconstruction to the
universal inclusion of `U` gives the morphism `contractingCoordinatesMap`.
Their composites with the ambient inclusion and positive multiplication are
proved to be the expected maps. Monicity of those two maps then proves the
two inverse identities in `positiveProductIso`. The closing two lemmas record
the ambient formulas for its forward and inverse morphisms.

The source uses the affine space underlying a vector group as a coordinate
scheme. The isomorphism is a scheme isomorphism over the base; it does not claim
that the generally noncommutative contracting group has an additive group law.
There is no field, localness, reducedness, connectedness, nontrivial-ring, or
nonempty-root-list assumption. The finite affine vector-quotient series and
the full split-Borel structural statement remain separate obligations.
