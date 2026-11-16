# Homomorphism rigidity from actual split root generators

This derived helper works over every commutative base ring, with arbitrary
nilpotents. Its source group is reductive. Its target is any group scheme
over the same affine base and need not be reductive or affine. The result
is about equality of actual morphisms, hence all relative test schemes.

`cellMap_comp_hom` applies a group homomorphism to the factors of a supplied
big-cell map. `hom_ext_of_open_cell` then proves equality of homomorphisms
that agree on the supplied coordinate torus and all maps in a family whose
cell is an open immersion. It uses the published `CellGluing.hom_ext_cell`,
smoothness and geometric irreducibility of a reductive group, and the
identity point of the coordinate cell. That extensionality theorem uses a
smooth covering by two cell factors, and so imposes no reduced-base
hypothesis. `hom_ext_of_rootParametrizations` obtains the open immersion
from the full actual fibrewise root datum and supplied root
parametrizations.

`AgreeOnWeylGenerators i P b u f F` packages agreement on the torus map,
on every simple-root map, and on each negative-simple point evaluated at
minus one over the base. The negative-root index is
`P.reflectionPerm a a`. The two images of the corresponding Weyl point
coincide because it is the product of two such negative points and a
simple-root point at one. Induction along a simple-root word propagates
the equality to every member of the Weyl family. If the given simple-root
parametrizations are Weyl-normalized, this family consists of actual root
parametrizations. `hom_ext_of_weylGenerators` now applies the preceding
root-family extensionality theorem.

The negative-simple-point hypothesis is explicit and is not deduced from
agreement on the positive simple roots. In particular this helper does
not yet prove pinned-isogeny uniqueness from a torus map and a pinning,
nor does it construct local torus conjugators. Those require further
structural isogeny comparisons. No field-only or reduced-ring comparison
is used as a substitute for equality over the arbitrary base ring.
