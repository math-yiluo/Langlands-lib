# Binary products of actual induced tori

This is an internal, derived construction for the product-kernel step of
Task 6659. Its mathematical inputs are the existing actual product of group
schemes, character-lattice Galois action, common finite Galois splitting field,
and transport of an induced-torus permutation basis. It adds no new field,
characteristic, perfectness, or splitting assumption.

`Langlands.CommGroupScheme.prod T U` is the actual commutative binary product
over an arbitrary base scheme. Its underlying group scheme is definitionally
`T.toGrp ⊗ U.toGrp`. Commutativity follows from the componentwise group law
under the existing multiplicative equivalence on every test scheme's points.
The factor inclusions and projections satisfy the four coordinate equations
and the additive decomposition of the identity. The latter is checked on
arbitrary test-scheme points by the two product coordinates.

`characterLattice.baseChangeProdEquiv` works after every morphism of base schemes.
Its forward map restricts a character to the two base-changed factor inclusions.
Its inverse adds the pullbacks of the factor characters along the base-changed
projections. The coordinate equations give one inverse identity, and the
decomposition of the product identity gives the other.
`baseChangeProdEquiv_galois` proves coordinatewise compatibility with the actual
character-lattice Galois action by the existing naturality theorem for character
restriction along a descended homomorphism.

`IsInducedTorus.isTorus` forgets the permutation basis and finiteness conditions
from the existing inducedness witness. `IsInducedTorus.of_iso` transports
inducedness along any isomorphism of underlying group schemes: base change
transports the split-torus witness, and pullback along the isomorphism carries
the character basis to a basis. Naturality of the actual Galois action ensures
that this basis remains permuted.

`IsInducedTorus.prod` proves binary-product closure over every field. Choose a
common finite Galois splitting field for the two actual tori. The existing
`IsInducedTorus.exists_permuted_basis` gives factor permutation bases over that
specified field. Their product basis has the disjoint union of the factor
index types as its index type. Pull it back through `baseChangeProdEquiv`.
The base-changed product is split by `baseChangeTensorIso` and split-torus
product closure. Coordinatewise Galois compatibility shows that each vector
coming from one factor is sent to another vector from that factor, while its
other coordinate remains zero. These data give precisely the unchanged
`IsInducedTorus` predicate.

Finally, `IsInducedTorus.of_product_iso` applies the closure result to any
commutative group scheme whose underlying group is isomorphic to the actual
binary product. This permits use with separately constructed product kernels.
The module proves these internal prerequisites; it does not construct a
z-extension or prove the domination statement.

The shared `IsInducedTorus.isTorus` theorem is imported from `Torus.Induced`;
the product construction does not redeclare it.
