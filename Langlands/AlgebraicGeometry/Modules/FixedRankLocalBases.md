# Fixed rank from free charts

This internal construction converts actual free charts on open neighborhoods into
`Langlands.Scheme.Modules.IsLocallyFreeOfRank`. Each chart uses a basis indexed by
`ULift (Fin n)`, and the resulting local generators retain exactly this index set.
No rank or local freeness assumption is added to the conclusion.

`freeOverIsoOfRestrict` carries a chart from the restricted scheme to the slice
site using Mathlib's equivalence `Scheme.Modules.overEquiv`. The definition
`freeNeighborhoodGenerators` uses one neighborhood per point; these cover the
scheme since each point lies in its chosen neighborhood. The generators are the
images of the canonical generators of the free sheaf under that chart. Their
presentation maps are isomorphisms, proving
`freeNeighborhoodGenerators_isLocallyFreeData`.

`isLocallyFreeOfRank_of_freeNeighborhoods` chooses the supplied charts, applies
the construction, and identifies each basis index with `Fin n` by `Equiv.ulift`.
This is the shared public home of the elementary slice-site construction
previously used privately in
`Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank`. That proof
and `Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof` import
these helpers in place of their duplicate constructions. This remains a derived
infrastructure result, with no additional source assertion.
