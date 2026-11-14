# The source torus and roots of a local-isogeny graph

This is derived support for general split-isogeny realization, implemented in
`RootDatumIsogenyRealization.SimpleIsogenyGraph`. It extends the common-torus
comparison-graph argument to different source and target tori and retains arbitrary
positive root factors. It is an internal construction, not a new statement
attributed to the literature.

## Hypotheses and result

Let `D : SimpleIsogenyGraph i i' t` be the actual source-simple local-isogeny
graph over a field `k`. Both ambient groups are smooth affine group schemes.
The source torus is split, as recorded by `D.split`. Suppose `P` and `P'` are
reduced root data on the actual lattices of the source and target tori, with
`hP : IsRootDatumOf i P`, `hP' : IsRootDatumOf i' P'`, a split target torus,
and `f : RootDatumIsogeny p P' P`. The actual torus map satisfies
`t ≫ χ = f.weightMap χ` for every target character. The finite index and
finite lattice hypotheses of this isogeny are retained.

`roots_eq_source` proves equality between the graph-torus roots and the
source-torus roots. It explicitly assumes connected reductivity of the source
and graph, maximality of the source torus, and maximality of the graph torus.
It does not derive graph reductivity from the supplied root map. The theorem
works over any field satisfying these hypotheses.

Over an algebraically closed field, `graphTorusGeometryOfReductive` constructs
`GraphTorusGeometry`, whose fields are the previously constructed full dynamic
factors, maximality of the actual graph torus, genericity of the chosen source
chamber in the graph, and the exact source-root equality. Graph reductivity
remains an explicit input; graph-torus maximality follows from the full factors.
The constructor does not assert that either graph projection is an isomorphism
or isogeny.

## Implemented proof

1. `roots_subset_union` uses both projections on actual dual-number tests.
   Each projection sends a graph weight vector to the same character weight
   for its induced source-torus action. If both ambient weight spaces vanish,
   joint injectivity of graph points forces the vector to vanish. The second
   ambient action here is the target action restricted through `t`.
2. `mem_roots_of_orthogonal` identifies roots of a local source centralizer by
   `dynamicCentralizerRoots`. Its closed local lift carries the nonzero weight
   space into the graph, using `roots_subset_comp`.
3. `reflection_mem_graph_roots` takes a source-root reflection representative
   from `IsRootDatumOf`. For a source simple root, the normalizer point
   centralizes its chosen direction, so it factors through that local
   centralizer and lifts to the graph. The resulting normalizing point
   transports weight spaces through the same character reflection.
4. `source_roots_subset` applies the published positive-root induction to the
   property that a character and its negative, when source roots, are graph
   roots. Simple roots lift by orthogonality. The double-root case is vacuous
   by reducedness of `P`, with torsion-freeness obtained from the root datum.
   The reflection case uses the lifted normalizers; genericity of the source
   chamber handles both signs.
5. `restricted_root_multiple` applies the split-torus weight-restriction
   theorem and `f.root_weightMap`. A restricted target root is
   `f.rootFactor j • P.root (f.indexEquiv j)`.
6. For any graph root on such a ray, the source root is already a graph root.
   The two characters are integrally dependent, witnessed by coefficients
   `1` and `-f.rootFactor j`. The published `rootReducedness` theorem on the
   reductive graph makes them equal or opposite. Both possibilities are
   source roots. The first ambient case of the union bound is immediate.

No restriction to separable isogenies or root factor one is used. The proof
uses no rational-point replacement of the full subgroup functors.
