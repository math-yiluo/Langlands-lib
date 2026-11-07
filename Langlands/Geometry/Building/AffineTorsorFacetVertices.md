# Finite actual facet vertices on affine torsors

This internal construction extends the vector-space finite vertex encoding of
`AffineFacetFiniteVertices` and `AffineFacetVertexIncidence` to an arbitrary real
affine torsor. The translation space `V : Type u` is a finite-dimensional real
normed vector space, while its affine torsor `A : Type v` may have an independent
universe. No topology or vector-space origin on `A` is assumed.

For any affine equivalence between affine spaces, full inverse-precomposition
transport of the actual roots preserves membership in the original sign-defined
facet closure. The helper `mem_facetClosure_transportedRoots_iff` follows from
the already published equality of the image of the entire closure. The existing
`isVertex_transportedRoots_iff` likewise preserves and reflects the actual
singleton-facet predicate.

The definition `torsorFacetClosureVertexFinset hΨ p` applies to a supplied
`IsAffineRootSystemWithRankZero Ψ`. Choose an origin in the nonempty torsor and
let `e : V ≃ᵃ[ℝ] A` be translation from that origin. Transport all roots through
`e.symm`, use the existing vector-space vertex finset at `e.symm p`, and map the
result back through the injective map `e`. The transported arrangement satisfies
all the corrected root-system axioms by `IsAffineRootSystemWithRankZero.transport`.

Its exact membership criterion is
`x ∈ facetClosure Ψ p ∧ IsVertex Ψ x`. Thus the finset contains all and only
the original actual incident vertices; the chosen origin and norm used to prove
finiteness introduce no auxiliary vertices. The finset is nonempty because the
vector-coordinate finset is nonempty. The construction includes rank zero and
does not assume that the root set is nonempty.

The same origin is used for both facets when comparing vertex finsets.
Injective finite-set mapping reflects inclusion. The vector-space incidence
theorem then gives inclusion between the transported closures, and injectivity
of the affine equivalence reflects this back to inclusion of the original
closures. Consequently containment of the two torsor vertex finsets is exactly
the existing affine face relation between their open facets. Equality of the
finsets is exactly the existing relation `facetRel`.

All arguments are derived from the named imported root-system and facet
transport results, finite vertex construction and affine incidence theorem.
No additional literature assertion is introduced. The result provides the
finite vertex encoding needed for genuine valuation apartments, which are
affine torsors rather than vector spaces. It does not construct a simplex or
factor decomposition, actual valuation data, a quotient realization, or any of
the five witnesses in `RootValuationBuildingConstructionStatement`.
