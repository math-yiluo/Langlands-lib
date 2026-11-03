# Uniform all-test solvability of split unipotent group schemes

This internal bridge uses the existing `HasSplitSeries`, `IsSplitUnipotent`,
and `IsSolvableScheme` predicates. It works over an arbitrary base scheme and
at every scheme universe. It adds no affine, field, or pointwise quotient
surjectivity hypothesis.

`derivedSeriesFunctor H n` assigns to every test scheme T the nth term of
the ordinary group derived series of H(T). Restriction preserves membership
because a group homomorphism carries each derived-series term into the
corresponding term. This construction is an actual subgroup functor; no
representability assertion is made for it.

`HasSplitSeries.derivedSeries_eq_bot` proves a uniform bound: a split series
of length n makes the nth derived series trivial on every test. In length
zero the existing definition says that the identity homomorphism has trivial
all-test range, so every point is the identity. In the successor step the
represented vector quotient has commuting point groups by its all-test
multiplicative equivalences with additive global functions. The quotient
homomorphism therefore kills all commutators. Its actual scheme-kernel range
is exactly the range of the smaller series subgroup. Every successive
commutator term lies in the image of the corresponding derived-series term
of that subgroup. Induction kills this image after n further steps.

The argument uses only the kernel-image clause of `IsFppfQuotient`. It does
not infer that the quotient map is surjective on each original test's point
group. The existing `mem_range_kernelι_iff` supplies the scheme-kernel to
pointwise-kernel identification.

`HasSplitSeries.derivedSeriesFunctor_eq_bot` states the same uniform result
as equality of actual subgroup functors. Finally,
`IsSplitUnipotent.isSolvableScheme` existentially packages the series length
as the single bound required by the existing `IsSolvableScheme` definition.
The result supplies a solvability prerequisite of the ordered-product
argument; it does not prove any realization or product isomorphism.

The provenance is internal: these are direct group-theoretic consequences of
the finite series, vector-group, kernel, and derived-series constructions
already in the Library. No additional literature assertion is introduced.
