# Jacquet projections from supplied literal Levi splittings

This internal adapter applies `HasCuspidalRemainderSplitting` and its
proved projection consequence to the proper standard Jacquet tests inside
each literal closed Levi. It is derived from
`CuspidalRemainderProjection`, `RationalLeviCuspidalRemainderTransport`,
and `FiniteCuspidalEmbeddingAssembly`. It makes no assertion of
unconditional splitting existence.

`LeviJacquetCuspidalRemainderSplittingTarget` is the explicit intermediate
condition that each actual normalized Jacquet module of every smooth
representation has the supplied cuspidal/remainder splitting for its
literal Levi. The cuspidal component is cuspidal for the proper standard
tests inside that Levi; its remainder has no nonzero cuspidal actual
subquotient. Source, root-index and group universes are independent.

`cuspidalJacquetProjectionTarget_of_splittings` obtains the two
projections from each supplied coproduct. The generic image argument makes
postcomposition with the cuspidal projection detect every map from a
cuspidal object in the source carrier universe. The cuspidal target alone
is raised by the equivariant `ULift` equivalence to carrier universe
`max uI uG uV`. Choosing these targets and maps gives exactly
`CuspidalJacquetProjectionTarget`, without imposing a length or
admissibility condition.

`finiteCuspidalInducedEmbedding_of_splittings` combines that adapter with
the published compact-limit localization injectivity and the existing
finite assembly's kernel argument. Its hypotheses explicitly retain
unimodularity of the radicals, their being limits of compact subgroups,
nonzero cuspidal Jacquet detection, and the local splitting condition.
It proves the generic `FiniteCuspidalInducedEmbeddingTarget` under those
hypotheses. This helper does not prove the closed rational embedding
statement or add hypotheses to it.
