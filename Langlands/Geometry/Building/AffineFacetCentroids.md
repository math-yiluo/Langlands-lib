# Centroids and least original faces in affine root arrangements

This unit derives affine averaging properties
directly from the existing original root-sign facet closures. It introduces
no additional assertion from the literature.

For a nonempty finite set of points in one original closed facet, its centroid
stays in that closed facet. Every point of the finite set lies in the closed
facet of the centroid, since root evaluations have a common weak sign and
cannot cancel in an average with positive equal weights. Consequently the
centroid belongs to another original closed facet exactly when all the points
do. Its closed facet is the least original closed facet containing those points.
These assertions apply to any root set on a real affine torsor, with independent
universes for its vector and point spaces.

For a corrected affine root system on a finite dimensional real affine torsor,
`facetCentroid` averages the entire existing nonempty finite set of actual
vertices of a closed facet. The centroid belongs to the original open facet
and agrees for two points exactly when their original facets agree. Applying
the centroid operation twice has the same result. The proof first uses the averaging theorem in
one incidence direction. In the other direction, every original vertex lies
in the centroid's closed facet; the published finite-vertex containment
equivalence then gives the reverse original incidence. Equality of the closed
facets identifies the original open facet.

Full affine root transport carries the existing finite vertex sets and their
canonical centroids to the corresponding ones on the target torsor. The finite
set identity follows from exact original closure and vertex membership under
transport. Affine naturality of the centroid follows because affine maps
commute with affine combinations whose weights sum to one. The vector and point
spaces of the target have independent universes as well.

This is a conditional geometric prerequisite. It does not construct a root
valuation, a building, or a polysimplicial decomposition. In particular a least
face containing a vertex subset need not have exactly that vertex subset.
