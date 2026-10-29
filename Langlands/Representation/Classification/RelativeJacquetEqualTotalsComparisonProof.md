# Proof of constituent Jacquet comparison from equal totals

`Langlands.glRelativeJacquetEqualTotalsComparison` proves the published
`Langlands.GLRelativeJacquetEqualTotalsComparisonStatement` with independent
universes `uF`, `uV`, `uW` and `uX`. This internal algebraic proof uses the
supplied composition series, admissibility of its grades and equal actual
Jacquet totals exactly as stated. Its provenance is the Library results
named below; no literal external-source proof is claimed.

The implemented proof decomposes the supplied actual inner and ambient totals
along the original series `s`, using `glRelativeJacquetFiltrationMultiplicity`.
This gives natural-valued functions `a` and `b` on `Fin l`, each summing to the
supplied common total `N`.

For each original grade, `glRelativeJacquetEmbedding` constructs an actual inner
count at most the supplied ambient count. Jordan–Hölder uniqueness identifies
that inner count with `a i`, so `a i ≤ b i`. The finite ordered-sum equality
criterion gives `a i = b i` at every index. No positivity or distinctness of the
grades is needed, and a repeated simple factor retains its separate index.

The selected actual subquotient is supplied by a surjective intertwiner
`q : U → μ`. The proof constructs its actual kernel-quotient representation
equivalence using the linear first isomorphism theorem and the intertwining
equations on quotient classes. `simpleSubquotientFactor` then locates `μ` as
an actual grade, without identifying its carrier universe with that of `A`.

The coarse representation equivalence descends to the actual refined opposite
Jacquet modules by the published `normalizedRefinedOppositeJacquetCongr`.
For the ambient modules, it first induces the equivalence with
`normalizedParabolicInducedEquiv`, then reuses
`Langlands.RelativeJacquetFiltrationMultiplicityProof.composedOppositeJacquetCongr`
to descend both this map and its inverse through the actual composed opposite
quotient. This existing helper uses the quotient-surjectivity lemmas to verify
that the descended maps are inverses. Finally,
`equivJordanHolderMultiplicityTransport` supplies actual finite-series
witnesses on the two Jacquet modules of `μ`, at the common count of that grade.

All four universes remain independent. The supplied series, grade admissibility
and equal actual totals remain premises of this algebraic result. The proof
constructs neither these hypotheses for generic induction nor positivity, the
quotient criterion or the strong irreducible head.
