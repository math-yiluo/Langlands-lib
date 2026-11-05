# Properties of base-changed scheme-theoretic intersections

This internal support module transports the geometric hypotheses needed for
the finite-field subgroup-product criterion along the existing canonical
`subgroupIntersectionBaseChangeIso`. The intersection is always the categorical
pullback of the actual group-scheme maps, including its nonreduced structure.

`isAffineHom_subgroupIntersection` obtains affineness from the closed pullback
projection to an affine first factor. `smooth_subgroupIntersection_baseChange`
first base changes the original smooth structure map, then transports
smoothness through the comparison isomorphism. The connectedness lemma applies
geometric connectedness of a smooth connected affine group over a field to the
original intersection, and transports its connected base change through the
same isomorphism.

For dimension comparisons, `Lie.linearEquivOfIso` uses postcomposition by a
group-scheme isomorphism and its inverse on the original dual-number identity
kernels. These maps preserve the existing scalar action. The inverse laws
are the two categorical inverse identities. `Lie.dimension_eq_of_iso` then
uses invariance of module finrank under this linear equivalence. This last
comparison requires affineness, without a smoothness or finite type assumption.

The provenance is internal and derived from the published intersection
construction, base-change preservation of smoothness, geometric connectedness
of connected finite type groups, and the actual Lie-kernel target maps.
No additional geometric premise is added to the finite-field target.
