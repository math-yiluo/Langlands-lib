# Normal solvable subgroups over an arbitrary field

This is an internal derived helper for the construction of a Levi centralizing a
maximal torus of a parabolic radical. It adds no structural assumption to the
published predicates.

`NormalSolvableCentralityStatement` is the universe-general proposition
described below; `normalSolvableCentrality` proves it using the helper.

`IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive_field` states
that a closed normal inclusion from a smooth connected affine solvable group
scheme into a connected reductive group scheme over any field is central.
Centrality uses the existing predicate on all relative test schemes.

The proof base changes to the chosen algebraic closure. Smoothness and affineness
are preserved by the pullback, and connectedness follows from geometric
connectedness of a smooth connected affine group. The published comparison
between geometric solvability and uniform all-test solvability preserves
solvability under this base change. Closedness, normality and connected
reductivity also persist. The algebraically closed theorem
`IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive` from
`Absolute.NormalSolvableCentrality` gives centrality there. The fpqc morphism from
the algebraic closure detects centrality by `IsCentral.of_baseChange`.

This proof does not assert that the subgroup is a torus or construct a radical.
Its provenance is the indicated composition of published Library results.
