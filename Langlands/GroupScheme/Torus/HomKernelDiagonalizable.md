# The actual kernel of a homomorphism of split tori

This internal construction treats any actual group-scheme homomorphism
`f : T → Q` between split tori over any commutative domain `k`, in an
arbitrary universe. It identifies the full scheme-theoretic kernel with
`D(X*(T) / image(f*))`. The image is the full image subgroup of the
pullback of characters. No saturation, dominance, primitivity or rank
condition is imposed. All torsion, including torsion in the characteristic,
is retained. No smoothness or connectedness of the kernel is asserted.

`characterLattice.comapHom` is pullback by composition with the actual
homomorphism. Its character evaluation formula holds on every test scheme.
For an arbitrary additive subgroup `N` of an abelian group, the
`subgroupAnnihilator` and `subgroupQuotientCharactersEquiv` constructions
identify characters of the quotient by `N` with characters killing all
elements of `N`. Restriction supplies the forward map, while the ordinary
quotient-group universal property supplies its inverse.

`homKernelCharacterPointsEquiv` evaluates a point of the actual represented
kernel on every character of `T`. Such an evaluation kills the image of
pullback because its image in `Q` is the identity. Conversely, the published
split-torus character point equivalence recovers a point of `T` from an
annihilating character. Character evaluation for the split target `Q`
detects that its image is the identity, so it is an actual kernel point.
The two inverse laws and multiplicativity are proved.

The character point model of the quotient diagonalizable group is the same
annihilator group. Both point equivalences are natural under every change
of test scheme. `homKernelDiagonalizableIso` applies the existing
`isoOfPointModels` construction to obtain the actual group-scheme
isomorphism. `homKernelDiagonalizableIso_inv` identifies evaluation after
the kernel inclusion with evaluation on the full quotient class.
`homKernelLattice_fg` transports finite generation from the character
lattice of a split torus and then takes the quotient.

The provenance is internal: the construction generalizes the published
single-character kernel model using the full image subgroup and its
quotient universal property. Its other inputs are the actual represented
kernel and split-torus character evaluation on all test schemes.
It does not extract components of the kernel, construct a torus covering,
or prove unipotent splitness or maximal-torus conjugacy.
