# Exact functors preserve actual smooth subquotients

The shared `Langlands.ExactSmoothTransport.map_isSubquotient` takes a functor
between smooth complex representation categories, its explicit
`MapsShortExactIntertwiners` hypothesis, and an actual
`SmoothRep.IsSubquotient B A`. It concludes the same actual relation between
the two image objects. Group universes are independent; both categories use
the same carrier universe. No particular derivative or Jacquet exactness is
assumed beyond the supplied generic hypothesis.

The proof maps the published injective/surjective presentation of the actual
subquotient. It uses `ExactSmoothTransport.map_injective` and the existing
`Derivative.LevelCalculus.map_surjective_of_exact`, now available from
[`ShortExactFunctorLaws`](../Derivative/ShortExactFunctorLaws.md).
The actual presentation criterion then gives the conclusion.

This is the shared elementary lemma from the independently accepted Worker 19
`CoarseJacquetExtraction` and `ExactFunctorIrreducibility` contributions. It is
placed here so both consumers use one declaration without importing each
other's applications. Its statement and proof argument are unchanged. The
old `ExactFunctorIrreducibility.map_isSubquotient` name is consolidated into
the `ExactSmoothTransport` name. The duplicate `map_surjective` helpers are
replaced by the existing `Derivative.LevelCalculus.map_surjective_of_exact`.

The direct dependencies are the generic image-filtration transport,
short-exact functor laws, and the actual subquotient presentation criterion in
`Classification.SupercuspidalSupport`. No new classification result or
representation-specific nonvanishing assertion is supplied.
