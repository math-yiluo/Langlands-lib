# Actual kernels and transport of natural vector coordinates

This internal support unit is derived from the Library's actual scheme kernel,
all-test represented subgroup functors, and the definitions in
`Rational.RootSubgroupStructureStatement` and `Rational.WeightSemigroupStatement`.
It introduces no structural result about reductive groups and has no additional
literature premise.

The module directly uses the published `Langlands.GroupScheme.mem_range_kernelι_iff` from the imported
`Langlands.GroupScheme.CentralIsogeny.Basic`. That theorem works over any base
scheme: the kernel image on any test is exactly the kernel of the induced
point-group homomorphism. Triviality of that image therefore gives
injectivity on every test and the categorical monomorphism of the underlying
map over the base. Similarly, taking the inverse image of the identity functor
under a monomorphism gives the identity functor.

For an fppf quotient by the actual trivial kernel, flatness, local finite
presentation and the monomorphism imply that its scheme map is an open
immersion, by Mathlib's `IsOpenImmersion.of_flat_of_mono`. Surjectivity then makes
it an isomorphism, and the forgetful functor from the over category reflects
this isomorphism. `IsFppfQuotient.isoOfBot` packages the resulting
isomorphism as a group-scheme isomorphism. This proof never assumes surjectivity on the point group of
an arbitrary test.

The remaining lemmas transport the definition's natural multiplicative
coordinate equivalences along group-scheme isomorphisms, including the canonical
isomorphism of two representatives of the same subgroup functor. Hence a vector
fppf quotient by the trivial kernel has vector source. Finally, the existence
part of `HasUniqueWeightVectorStructure` supplies `IsVectorGroup` after forgetting
the torus action and uniqueness assertion. All constructions retain the base
scheme universe; the coordinate transport and quotient statements allow any
base scheme.

`IsVectorGroupOfDimension.of_iso_source` transports vector coordinates from
the target of an isomorphism to its source; the opposite-direction interface
in `SplitUnipotentTransport` remains available separately.
