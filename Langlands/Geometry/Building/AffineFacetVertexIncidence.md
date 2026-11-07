# Actual affine face incidence in finite vertex coordinates

This is an internal extension of `AffineFacetFiniteVertices`, derived from the
existing sign definitions and finite convex-hull theorem. It uses no additional
literature assertion. All closures, vertices and faces belong to the original
affine root arrangement.

For any affine root family on a real affine space,
`facetClosure Ψ p ⊆ facetClosure Ψ q` holds exactly when `p` belongs to the
second closure. One direction evaluates the containment at `p`; the other uses
transitivity of the weak sign conditions. Equality of the two closures is
equivalent to `facetRel Ψ p q`: mutual weak sign conditions force equality of
every root sign. Thus a closed facet determines its original open facet.
The existing predicate `IsFaceOf Ψ (facet Ψ p) (facet Ψ q)` is exactly this
containment of closures. Its defining witness of an upper-facet point gives
the same upper closure because that closure depends only on the facet.
These algebraic results allow independent vector and affine-space universes
`u` and `v` and require no local finiteness.

On a finite-dimensional real normed vector space, suppose the arrangement is
locally finite and the two specified facet closures are compact and convex.
The finite convex-hull identity from `AffineFacetFiniteVertices` then shows that
one closure is contained in the other exactly when its actual incident vertex
set is contained in the other's. The forward implication retains each point's
vertex property; the converse takes convex hulls of the vertex containment.

For a supplied `IsAffineRootSystemWithRankZero Ψ`, compactness and convexity of
the closures discharge those premises. The resulting finite-set statements are:

- `facetClosureVertexFinset hΨ p ⊆ facetClosureVertexFinset hΨ q` is equivalent
  to closed-facet containment and hence to the original affine face incidence.
- The two vertex finsets are equal exactly when `facetRel Ψ p q`.

`closedFacetVertexFinset hΨ C` assigns finite vertex coordinates to a member
`C` of `Set.range (facetClosure Ψ)`. It chooses a representing point, but its
membership theorem is precisely `x ∈ C.val ∧ IsVertex Ψ x`, so the result
depends only on the closed facet. The definition
`closedFacetVertexOrderEmbedding hΨ` embeds the original closed facets, with
their inherited subset order, into `Finset V`, ordered by inclusion. Both
preservation and reflection of order follow from the preceding equivalence.
An interval below the closure of `p` embeds into the finite powerset of
`facetClosureVertexFinset hΨ p`; consequently each closed facet has only
finitely many incident closed faces.

The topology and finite-vertex results hold at every vector-space universe `u`
and include rank zero. The closed facets here are the existing sign-defined
closures. Inclusion between the original open facets is not used as a face
order. The contribution establishes finite vertex coordinates and finite lower
intervals, without asserting that every vertex subset is a face. In particular,
it supplies no simplex or polysimplicial factor decomposition, original
apartment coordinate-mixing theorem, quotient realization, or proof of
`RootValuationBuildingConstructionStatement`.
