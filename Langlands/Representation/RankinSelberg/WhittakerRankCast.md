# Equality transport of Whittaker functions

`Langlands.RankinSelberg.InducedTailIntermediate.whittakerRankCast` transports
an actual Whittaker function along an equality of rank indices. Its definition
is equality substitution `h ▸ W`, so it retains the coefficient function.
`whittakerRankCast_apply` evaluates the transported function after the
corresponding numerical matrix reindexing.

These declarations are moved unchanged from
`InducedTailIntermediateCoefficientAdapters`, with their original namespace.
That module imports this pair and retains the inverse-coefficient adapters,
coefficient-image membership lemmas, character recastings and cutoff application.
`RankOneExtensionSpanTransfer` also imports this pair and uses the same rank cast
through its `rankCastWhittaker` abbreviation. The shared module depends only on
`QuotientIntegrals` and `RankReindex`, so this reuse adds no dependency on the
intermediate-tail or cutoff comparison to the rank-one transfer construction.

The construction is an internal equality transport. It asserts no integral,
measure, convergence or span comparison. The evaluation proof substitutes the
rank equality and uses extensionality of the underlying matrix units.
