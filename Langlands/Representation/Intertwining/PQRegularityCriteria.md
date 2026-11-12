# The kernel and forward-exponent clauses of Renard VII.3.3

Worker 154. `PQRegularityPredecessorCriteriaStatement` isolates the first two clauses of the
published regularity lemma. The module proves this specialization as
`pqRegularity_predecessorCriteria`, for the original regularity quotient and every
supplied full geometric piece at a strict Bruhat predecessor of identity.
Its source is Renard 2026, 9 July edition, VII.3.3, printed pp.234–235 /
PDF pp.240–241.

The proof constructs the actual quotient filtration, chooses its natural grade
comparisons and transports the intersection of the action kernels along the
complete equivalence between the finite grade indices and strict predecessors.
The filtered kernel criterion yields the stated equivalence. The forward
spectral implication follows from comaximality on each grade and smoothness
of the normalized induced piece; the published compact-open weight predicate
is retained. No finite-length or admissibility assumption is used.

This helper does not assert the converse from finite length and disjointness.
