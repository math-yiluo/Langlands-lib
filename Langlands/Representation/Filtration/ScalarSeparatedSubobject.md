# Scalar-separated simple series of actual subobjects

Let `A` and `B` be actual smooth representations over an arbitrary field, with
independent coefficient, group and carrier universes. Suppose `A` has a
supplied finite simple series such that one group element `z` acts through
pairwise distinct scalars on its graded factors, `B` has finite group-algebra
length, and an actual injective intertwiner maps `B` into `A`.

`exists_scalarSeparatedSeries_of_injective` produces an actual simple
series of `B`, together with an injective map from its factor indices into
those of the supplied series of `A`. The scalar on each factor of `B` is
the scalar at its matching index in `A`. Centrality of `z` is unnecessary
for this extraction; when `z` is central the result is a series to which
central eigenspace splitting applies. `scalarSeparatedSeriesOfInjective`
chooses and bundles that actual series, the index map and all the stated
properties.

The proof chooses a simple series of `B` from its finite length.
Equivalence of two factors of `A` would equate their scalar actions on a
nonzero vector, so the supplied series is multiplicity free.
Jordan–Hölder multiplicity is monotone along the actual injection. Each
factor of the chosen series of `B` therefore has positive multiplicity in
the series of `A`, and hence is equivalent to some actual graded factor.
The multiplicity bound of one makes these matching indices injective:
two equal matches would give two occurrences of the same factor in `B`.
Actual factor equivalences transport the scalar actions.

The substantial imported results are the actual composition-series choice
from `Smooth.IrreducibleCompositionFactors`, generic scalar transport and
nonzero vectors of simple representations from
`Filtration.CentralEigenspaceSplitting`, and injective multiplicity
monotonicity and the multiplicity-one bound from
`Filtration.MultiplicityFreeSubmoduleLatticeProof`. The provenance is
internal group-algebra Jordan–Hölder theory. No literature assertion is
transcribed and no parabolic or classification result is used.

Author: Worker 1186.
