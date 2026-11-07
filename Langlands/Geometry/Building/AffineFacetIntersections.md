# Intersections of original closed affine facets

Work on a finite dimensional real normed translation space and an affine torsor
over it, with independent universes for vectors and points. The supplied root
set satisfies the existing corrected `IsAffineRootSystemWithRankZero`
predicate. All facets, closed facets and vertices are the original sign-defined
objects. Rank zero is included.

`facetClosure_inter_nonempty_iff_vertexFinset_inter_nonempty` says that two
original closed facets meet if and only if their finite actual vertex sets
intersect. To prove the forward direction, take a point in the intersection and
an actual vertex in its closed facet. Transitivity of original closure incidence
puts that vertex in both given closed facets. The reverse direction follows
from the exact actual-vertex membership criterion.

`facetIntersectionCentroid` averages the common actual vertices. Its geometric
properties require nonempty intersection; no intersection property is asserted
for its value when the intersection is empty.
`facetClosure_facetIntersectionCentroid` identifies its original closed facet
with the intersection. Averaging puts the centroid in both closed facets, so its
closed facet is contained in the intersection. For the reverse inclusion, each
point in the intersection has every actual incident vertex among the common
vertices. The no-cancellation centroid theorem puts those vertices in the
centroid's closed facet. Reflection of closed-facet containment by actual vertex
containment then puts the point there as well.

`vertexFinset_facetIntersectionCentroid` identifies the resulting actual vertex
finset with exactly the intersection of the two input finsets.
`facetCentroid_facetIntersectionCentroid` shows that the chosen representative
is the canonical centroid of its own original facet.
`exists_facetClosure_eq_inter` records closure of the family of original closed
facets under nonempty binary intersection. The centroid is symmetric and
depends only on the two original facet classes.

`facetIntersectionCentroid_transportedRoots` proves naturality for a full
transport of the affine root set under an affine equivalence. Exact transport
of actual vertices preserves their finite intersection, and normalized affine
averaging commutes with that equivalence. The source and target vector and point
types have four independent universes. The naturality theorem retains the
nonempty-intersection premise.

This is a derived internal geometric result. It uses the existing finite actual
vertex, incidence, centroid and affine-root transport theorems and introduces no
new literature assertion. It does not construct an affine root system, a
valuation datum, a polysimplicial decomposition, or the five witnesses of the
host root-valuation construction statement.
