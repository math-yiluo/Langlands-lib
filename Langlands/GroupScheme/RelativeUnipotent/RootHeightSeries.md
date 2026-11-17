# Finite vector-bundle series from positive root-height charts

Worker 204, Task 7200. This internal derived unit assembles the finite
series supplied by a `RootHeightChart` over an arbitrary commutative ring
at arbitrary universe. Chart existence for a relative radical and descent
of locally constructed filtrations are separate obligations.

An index exceeding every root height gives the bottom ambient subgroup.
The represented inclusion is monomorphic, so every point of the represented
term is the identity. This proves `range_id_eq_bot` on every scheme test.
At height one, positivity says that the ambient subgroup is the full group.
The represented-subgroup uniqueness isomorphism therefore identifies the
height-one term with the original group scheme.

`hasVectorBundleSeries_of_bound` applies the finite-segment theorem to
height terms starting at one. Every successive inclusion is closed,
its source is smooth, and its pointwise range is normal. The actual
exact-height quotient is an fppf quotient with that range as its full kernel,
by `RootHeightKernel`. The quotient is a polynomial vector group; the
published free-vector-bundle comparison identifies its points naturally
on all tests with sections of an actual finite free module sheaf.
The terminal triviality criterion closes the recursion, and the height-one
group-scheme isomorphism transports the series to the original group.

`heightBound` is the maximum of the finitely many heights, defined as zero
for an empty family. Each height is below its successor, so the preceding
result yields `hasFiniteVectorBundleSeries` and the chosen `seriesWitness`
of precisely that length. Empty layers and an empty root family are
included. The provenance is the preceding represented root-height
construction together with the Library's finite-segment, transport,
represented-subgroup uniqueness and free-vector-bundle theorems.
No additional literature result is used.
