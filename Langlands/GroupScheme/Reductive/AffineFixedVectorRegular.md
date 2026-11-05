# Normalized regular maps for arbitrary affine groups

This internal construction removes the supplied corepresentation from the
normalized coefficient map in `FixedVectorRegularCoefficient`. It applies to
an arbitrary field `k : Type u`, an actual affine group scheme `G` over `k`,
and a finite coordinate representation of `G` indexed by a small finite type.
It uses neither finite type nor smoothness, reductivity, algebraic closedness
or a characteristic assumption.

`Intertwines.points` converts the existing affine-algebra-test intertwining
predicate into the same matrix identity on every relative test scheme. It
chooses an affine presentation of the acting group, transports its affine
matrix identity through the canonical global-section isomorphism, and pulls
the resulting identity back along the given group point. Scalar naturality
identifies the coefficient maps. Only the acting group is assumed affine;
the test scheme is unrestricted.

`affineRegularRepresentation` uses the existing `AffineCoordinates` coordinate
algebra and corepresentation of `G`. It transports the finite regular-subspace
representation to `G` along the inverse of `AffineCoordinates.groupSchemeIso`.
Its inputs are a subspace, a finite basis and stability under contraction in
the second tensor factor, for precisely the coalgebra constructed from that
corepresentation. No additional group action is assumed.

`exists_affine_finite_regular_map_to_one` takes a nonzero vector fixed on every
scheme test by the given representation. It constructs a finite regular
subspace of the chosen coordinate algebra, a basis and a matrix intertwiner
into its actual representation of `G`. The basis expansion of the image of
the vector is the constant regular function one. The proof restricts the
representation and fixedness to the corepresented model, applies the existing
normalized coefficient construction, and transports the intertwining equation
back through the group isomorphism. Together with `Intertwines.points`, the
resulting map is equivariant on every scheme test.

The provenance is internal: the only new arguments are the global-section
naturality calculation and transport along the published affine-coordinate
group isomorphism. The normalized coefficient map and finite regular span are
provided by the imported construction. This result does not assert that the
map is injective. It does not construct Steinberg modules, a map to their
endomorphisms, or a separating invariant, and does not prove Haboush's theorem.
