# Finite-presentation atlases on clopen dimension restrictions

This derived supporting unit for Conrad's Theorem 5.9 constructs actual atlases
on the source and target restrictions defined in `SmoothDimensionRestrictions`.
Its inputs and conclusions concern the ordinary quotient point topology.
It assumes no point-count estimate or adelic openness theorem.

For an open subset of the points of an algebraic space, `chartToSpace` maps the
actual inverse-image open subscheme of a scheme chart into the selected open
subspace. The equality of represented subfunctors from
`SmoothDimensionOpenSubspaces` proves that its square with the original chart
is cartesian. Etaleness and surjectivity of the chart pass to this square by
base change.

When the point subset is also closed, its inverse image in a compact scheme
chart is closed and compact. Over an affine base, a locally finitely presented,
quasi-compact atlas therefore restricts to one with both properties: the open
immersion preserves local finite presentation, and compactness of its source
implies quasi-compactness of its structure morphism. Separatedness is inherited
by pulling back the ambient diagonal along the monomorphic inclusion.
Quasi-separatedness uses the existing open-subspace theorem.

The target dimension loci are clopen by local constancy. Their inverse images
under the continuous source-to-target point map are also clopen. The preimage
identity for point-selected subfunctors identifies the latter with the actual
source restrictions, so both families inherit finite-presentation atlases,
separatedness and quasi-separatedness from the corresponding original space.

The provenance is internal: actual scheme opens and subfunctor pullbacks from
`SmoothDimensionOpenSubspaces`, the source restriction from
`SmoothDimensionRestrictions`, and the existing relative morphism-property,
diagonal and scheme compactness interfaces. Uniform Lang–Weil and the final
adelic theorem remain separate obligations.
