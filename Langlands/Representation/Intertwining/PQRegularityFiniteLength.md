# Conditional finite-length assembly for PQ regularity

This is an internal reduction toward the exact Renard VII.3.3 target. It retains
both `LeviJacquetFiniteLengthStatement.{u,v}` and
`LeviInductionFiniteLengthStatement.{u,v}` as explicit global premises and
concludes the unchanged `PQRegularityLemmaStatement.{u,v}`.
`PQRegularityFiniteLengthReductionStatement` is this implication, and
`pqRegularity_finiteLength_reduction` proves it. Neither premise is proved by
this unit, and the unit does not establish the unconditional regularity target.
Its provenance is the composition of the represented-parabolic finite-length
interfaces, the actual predecessor filtration and the central-action algebra
argument, rather than a separate translation of a source assertion.

`GeometricLemmaIntersectionDatum.pieceFunctor_finiteLength` proves finite
length of the full geometric piece, conditionally on these same two premises.
It applies the Jacquet preservation premise inside the original source Levi,
pulls back along the datum's continuous conjugation equivalence using the
published finite-length transport theorem, and applies the induction
preservation premise inside the target Levi. The conclusion concerns the
original full piece's group-algebra module, including normalized induction.
It does not substitute the inducing Jacquet representation for that piece.

`finite_splitComponent_actionQuotient` specializes finite central-action
algebras to an actual Levi and its split component. Smoothness and affineness
of the connected reductive Levi give the finite-type rational-point topology.
The published rational-point results give local compactness, second
countability and the topological group structure; hence the group is
sigma-compact. The actual point map of the split component has central image.
`PQFiniteLengthAction.finite_actionQuotient` now gives finite dimensionality of
the original faithful action quotient for a finite-length smooth
representation. This specialization has no admissibility premise.

The assembly theorem obtains the first two clauses of the exact target from
`pqRegularity_predecessorCriteria`. For the converse, it uses
`exists_pqRegularity_pieceFiltration` to enumerate all strict predecessors and
filter the actual regularity quotient with naturally isomorphic full geometric
grades. The conditional piece helper gives finite length of each grade model.
The central-action specialization gives finite-dimensional faithful action
quotients for both the original representation and every full piece. Their
smoothness is the original-action smoothness proved in `PQRegularityCriteria`.
The theorem reindexes the supplied disjointness hypothesis along the complete
predecessor enumeration and applies `pqRegularity_of_disjoint_weights`.

The field universe `u` and source-carrier universe `v` are unchanged. Full piece
carriers have universe `max u v`, and the central-action specialization is used
at that universe when needed. No additional input at a shifted carrier
universe is assumed for the two preservation statements. In particular this
conditional reduction leaves their unconditional proofs, and the later exact
proof submission for `PQRegularityLemmaStatement`, outstanding.
