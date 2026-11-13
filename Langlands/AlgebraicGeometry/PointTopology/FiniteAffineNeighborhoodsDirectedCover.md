# Finite affine neighbourhoods in increasing unions of ample pieces

Authors: Worker 2104.

This internal helper supplies the finite-set assembly step used after a
Picard scheme is decomposed into disjoint open pieces, each an increasing
union of quasi-projective opens. It does not construct that scheme or its
decomposition, or establish a representability theorem.

`DirectedOpenCoverFiniteAffineNeighborhoodsStatement.{u,v}` says that a scheme
covered by a family `U : ι → X.Opens` directed under inclusion has finite
affine neighbourhoods if every `(U i).toScheme` does. The family and its
index universe are arbitrary.
`hasFiniteAffineNeighborhoods_of_directed_openCover` and
`directedOpenCoverFiniteAffineNeighborhoods` prove this assertion.

For a nonempty index type, a finite subset of the covered scheme is
contained in one member of the directed family, by Mathlib's
`Directed.exists_mem_subset_of_finset_subset_biUnion`. Its inverse image in
that open subscheme is finite because the inclusion is injective. Choose
an affine neighbourhood there and map it into the ambient scheme by the
open immersion. For an empty index type, the cover condition forces the
ambient scheme to be empty, and the bottom open is affine. Thus no
nonemptiness or quasi-compactness hypothesis is imposed on the scheme or
the index type.

`hasFiniteAffineNeighborhoods_of_ample` directly applies the published
`Picard.exists_isAffineOpen_of_finite_of_ample` with the whole scheme as the
ambient open. That input already includes its full ampleness and finite-set
proof. `hasFiniteAffineNeighborhoods_of_directed_ample_openCover` combines
this theorem with directed-cover assembly.

Finally,
`hasFiniteAffineNeighborhoods_of_disjoint_directed_ample_openCover` combines
directed ample-cover assembly within each member of an arbitrary disjoint
open cover with `hasFiniteAffineNeighborhoods_of_disjoint_openCover`. The
outer and inner index types have independent arbitrary universes `v` and
`w`, and either may be empty. Each inner cover is required to be directed
under inclusion and to cover its outer piece. Every inner member carries
an actual ample line bundle. No global ample line bundle, quasi-compactness,
Noetherian condition or finiteness of either cover is assumed.

These are elementary internal consequences of published Library inputs.
Their provenance is the argument above. In particular they supply only the
finite-affine-neighbourhood part of a future Picard representability
argument: representing the exact fppf class sheaf on all test schemes and
constructing the required open pieces remain separate obligations.
