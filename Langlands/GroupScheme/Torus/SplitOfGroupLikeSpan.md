# Split affine tori from group-like spanning

This internal result applies in arbitrary universe `u` to a field `k` and an
actual affine group scheme `T` over `Spec k`. If `IsTorus T` and the group-like
elements span its actual coordinate Hopf algebra over `k`, then
`IsTorus.isSplitTorus_of_groupLike_span` proves `IsSplitTorus T`.

The construction `AffineCoordinates.splitIsoOfGroupLikeSpan` takes an explicit
splitting over an extension `K/k`, indexed by a finite type `I`, and the spanning
condition. It returns an actual isomorphism over `k` with the split torus on
the same index type `I`. The theorem applies it to the witness in `IsTorus`.

The auxiliary `Langlands.GroupLike.mulEquivOfBialgEquiv` transports group-like
elements and their multiplication through any bialgebra equivalence.

Choose a splitting field and an isomorphism of the scalar extension of `T`
with the finite split torus indexed by `I`. The published Hopf base-change
comparison and diagonalizable Hopf comparison identify the extended coordinate
Hopf spectrum with the standard spectrum of `K[ℤ^I]`. Full faithfulness of
relative Hopf spectrum recovers the equivalence of coordinate Hopf algebras.
Since the group-like elements already span before extension, the published
scalar-extension equivalence identifies their group with the group-like
elements after extension. The latter group is exactly the monomial group
`ℤ^I`. This gives a finite integer lattice for the original character group.

Reconstruction of a bialgebra spanned by group-like elements expresses the
original coordinate Hopf algebra as the group algebra of that character group.
The actual affine coordinate comparison, followed by the diagonalizable Hopf
comparison and the lattice split isomorphism, gives the required isomorphism
of actual group schemes with `𝔾_m^I`.

The provenance is internal composition of the published coordinate,
scalar-extension, group-like reconstruction and diagonalizable comparison
constructions. The spanning condition is an explicit hypothesis: no general
spanning descent, separably closed splitting theorem or unrestricted
dynamic-centralizer reductivity theorem is asserted here.
