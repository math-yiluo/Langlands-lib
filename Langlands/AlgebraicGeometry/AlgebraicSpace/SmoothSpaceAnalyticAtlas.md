# Analytic atlases on smooth algebraic-space points

This internal construction implements the chart-gluing step of Conrad's Proposition 5.4 (printed pp.15–16). For each complete nontrivially normed field, each natural dimension and each algebraic space satisfying the unchanged `IsSmoothPureDimensional` predicate, it constructs a charted space on the actual rational-point carrier, for the published etale-chart topology, and proves that this is an analytic manifold over that field.

An affine etale source with a rational lift and the prescribed smooth relative dimension is chosen above each point. Its point map is a local homeomorphism for the existing topologies. Composing an inverse branch with the source's regular analytic chart gives an open partial homeomorphism into `Fin n → K` containing that point. The range of these chosen charts is the atlas.

For two such charts, the common affine refinement construction identifies the transition between their inverse branches with the second projection composed with an analytic local inverse of the first. Composing with the analytic source charts and their inverses proves analyticity on every point of the overlap. Mathlib's analytic atlas criterion then proves the manifold assertion.

`canonicalAnalyticPointStructure` packages this family; `canonicalAnalyticPointStructure_isAnalytic` proves its manifold component. No field characteristic, positive-dimension, nonempty-point-space, or global affine hypothesis is imposed. Functoriality, etale local isomorphisms for the family, affine-space normalization and uniqueness of admissible families remain to be proved.
