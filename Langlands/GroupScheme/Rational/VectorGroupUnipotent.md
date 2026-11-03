# Coefficient-representation unipotence of vector groups

This internal adapter proves the existing `IsUnipotent` predicate for every
group scheme with the existing natural finite-dimensional vector coordinates.
It works over every field in universe `u`, in every characteristic, including
dimension zero. No affineness, smoothness or connectedness premise is needed in
the final vector-group results: these properties follow from the coordinates.

`IsWeightVectorCoordinates.homogeneousCoordinatesOfWeight` packages a supplied
single-weight coordinate system as homogeneous vector coordinates whose weight
labels are all the supplied character. The coordinate system is already assumed
to be equivariant on every scheme test; this construction makes no assertion
that an arbitrary torus action can be linearized.

The coordinate basis of the actual Lie kernel lies in the supplied weight
space. Expanding any Lie vector in that basis shows that this weight space is
the whole Lie space. For a split torus, the published independence theorem for
actual weight spaces then shows that the zero weight space vanishes when the
supplied character is nonzero. These intermediate weight-space lemmas use the
affineness instance needed to define the actual Lie spaces.

For the standard polynomial vector group, take the existing action of `Gm`
through its identity character. That character is nonzero because the published
additive equivalence from endomorphisms of `Gm` to the integers sends it to one.
Thus the proof does not choose a nonidentity ground-field unit and works over
finite fields too. The standard natural coordinates have precisely this single
weight. The published `torusActionUnipotence` theorem applies to its smooth,
connected affine group scheme and proves the actual coefficient-representation
unipotence predicate.

`IsVectorGroupOfDimension.isUnipotent` transports that result through the actual
group-scheme isomorphism supplied by natural coordinates.
`IsVectorGroup.isUnipotent` forgets the chosen dimension.

The provenance is internal: the proof composes existing coordinate, Lie basis,
split-torus weight-independence, torus-action unipotence and isomorphism-transport
results. This adapter supplies a prerequisite for the solvable maximal-torus
conjugacy task; it does not prove that task, stable-vector existence or
linearization of arbitrary torus actions.
