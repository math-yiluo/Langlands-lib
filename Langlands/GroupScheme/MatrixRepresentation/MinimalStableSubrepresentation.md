# Minimal stable subspaces and actual simple subrepresentations

This internal construction supplies the first simple constituent needed for the
composition-factor argument in KP Lemma 2.2.11 (printed pp.72–73, PDF pp.103–104,
*Bruhat–Tits theory: a new approach*, 2023). It is a derived finite-dimensional
construction and makes no complete-reducibility assertion.

The bottom and top coordinate subspaces are stable in the published
all-affine-tests sense. `IsStableSubspace.map` proves that an actual intertwiner
maps stable subspaces to stable subspaces: applying a ground-field linear
functional to a translated vector commutes with the intertwining matrix.
`range_coordinateInclusion_eq` identifies the image of split subspace
coordinates from their columns and projection identity.

`exists_minimal_nonzero_stableSubspace` minimizes the natural-number dimension
among nonzero stable subspaces. Any nonzero stable subspace inside a chosen
minimizer has at least its dimension, hence equals it.
`minimalNonzeroStableSubspace` chooses one such subspace, and its specification
theorem records these three properties.

For an affine group, `exists_simple_subrepresentation` chooses the published
split coordinates of this minimal subspace and the actual representation they
induce. Its inclusion is an injective intertwiner with exactly the minimal
subspace as image. Images of stable subspaces of the restricted representation
are therefore zero or the minimal subspace. Injectivity of the inclusion
reflects these alternatives to zero or the whole coordinate space. The
restricted space is nontrivial because its image is nonzero.

The conclusion exposes nontriviality and the all-test stable-subspace
alternative explicitly, so it can be folded into the actual irreducibility
predicate without adding a second such definition. The source field is
arbitrary and the group need only be affine. This unit does not construct a
whole composition series, prove a common kernel finite, or prove spectral
boundedness.
