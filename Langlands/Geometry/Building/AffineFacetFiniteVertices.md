# Finite actual vertices of compact affine facets

This is an internal extension of `AffineFacetVertexGeneration` and
`AffineFacetCompactness`. It uses the existing root arrangement, zero-dimensional
facet predicate and sign-defined facet closures. The arguments are derived from
the imported definitions and the existing local sign-stability and compact
convex-hull results; no additional literature assertion is used.

For a locally finite reflection arrangement on a real vector space, the roots
vanishing at an actual vertex determine that vertex uniquely. If they all
vanish at a second point, a sufficiently short segment toward that point
preserves every root sign at the vertex. Its endpoint lies in the singleton
facet of that vertex. Positivity of the segment parameter then forces the two
points to coincide. Consequently the map sending an actual vertex to its set
of vanishing roots is injective.

On a finite-dimensional real normed space, `rootsMeetingSet Ψ C` consists of
the roots in the original arrangement whose zero hyperplanes meet `C`. When
`C` is compact, each linear functional has bounded absolute value on `C`.
For a root vanishing somewhere in `C`, its value at the origin is the negative
of its derivative evaluated at that point. The arrangement's bounded-root
finiteness therefore makes `rootsMeetingSet Ψ C` finite. Every vertex in `C`
has its vanishing-root set in the finite powerset of this set. The preceding
injectivity proves that `C` contains only finitely many actual vertices.

In particular, the incident vertices `facetClosureVertices Ψ p` of a compact
facet closure form a finite set. The imported `AffineFacetVertexGeneration`
result identifies any compact convex facet closure with the closed convex hull
of those vertices. A finite set has closed convex hull in a finite-dimensional
real normed space, so the closure operation can be removed:
`convexHull ℝ (facetClosureVertices Ψ p) = facetClosure Ψ p`.
Since the closure contains `p`, its incident vertex set is nonempty.
Compactness and convexity remain explicit hypotheses for these arrangement
results; local finiteness alone does not imply compact facet closures.

For a supplied `IsAffineRootSystemWithRankZero Ψ`, the imported affine
compactness result and convexity of sign-defined facet closures discharge those
two hypotheses. The definition `facetClosureVertexFinset hΨ p` constructs the
finite set of all actual vertices in that closure. Its membership theorem is
exactly `q ∈ facetClosure Ψ p ∧ IsVertex Ψ q`; the finset is nonempty and its
convex hull equals the original closure. These results hold at every vector
space universe `u`, with no positive-rank or nonempty-root premise.

This contribution gives finite vertex sets for the original affine geometry.
It does not assert that each irreducible facet is a simplex, construct a
polysimplicial factor decomposition, or prove coordinate mixing of a realized
building apartment. Those steps, the actual quotient realization and the
unconditional `RootValuationBuildingConstructionStatement` remain separate
obligations.
