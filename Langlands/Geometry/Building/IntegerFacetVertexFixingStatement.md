# Fixing closed facets through their original vertices

`IntegerFacetVertexFixingStatement` is an unproved internal geometric
prerequisite for finite vertex approximation. It quantifies over an arbitrary
field `k : Type u`, an explicit integer-valued valuation, an affine group scheme,
and supplied `IntegerValuationBuildingData`. These data already include
connected reductivity, a maximal split torus, its KP apartment and the
centralizer compatibility for that same valuation.

Two further premises are explicit: the ordinary affine roots form the corrected
affine root system, including rank zero, and its affine Weyl group is contained
in the image of the actual normalizer action. No existence proof for either
premise is asserted here.

The conclusion `B.ClosedFacetsFixedByVertices` uses the original apartment map
into the original reduced quotient. For each apartment point `p` and each
original rational group element `h`, if `h` fixes the image of every original
apartment vertex in the weak-sign closure of the facet of `p`, then it fixes
the image of every point of that closure. The element need not stabilize the
apartment or act on it by one supplied affine map. The conclusion concerns the
full rational-point fixer, without a character-kernel restriction.

The statement is internally derived as the missing geometric step in the
finite-vertex approximation route: once vertices of all closed facets meeting
a bounded subset form a finite invariant set, this fixation implication puts
their common fixer inside the fixer of the original subset. It is stronger
than the single-point consequence needed in that application. A proof may use
convexity of fixed loci or simultaneous apartment transport, but neither is
assumed or proved in this pair.

The published affine-map criterion
`AffineRootSystem.eqOn_facetClosure_of_vertex_fixing` works in vector
coordinates for an already supplied continuous affine map. It does not prove
this statement for an arbitrary rational element of the quotient action.
No local-field instance on a maximal unramified field, integral model,
building metric or independent geometric result is introduced by the statement.
