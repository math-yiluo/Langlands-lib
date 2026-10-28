# Finite-series multiplicities for opposite Jacquet filtrations

`Langlands.Parabolic.normalizedOppositeJacquetFiltrationMultiplicity`
proves the exact proposition
`Langlands.Parabolic.NormalizedOppositeJacquetFiltrationMultiplicityStatement`
with independent universes `uF`, `uV`, and `uW`.

The proof first establishes a private algebraic helper. It takes an actual
finite invariant filtration `s` of a representation `A`, representations
`pieces i`, and actual representation equivalences from the graded
quotients of `s` to `pieces i`. For any constituent representation `τ`,
it constructs the equivalence between a finite-series multiplicity `m`
in `A` and finite-series multiplicities in all `pieces i` whose counts
sum to `m`.

In the forward direction, the supplied
`HasJordanHolderMultiplicity A τ m` contains an actual composition
series and its length `N`. The proof passes that series to
`jordanHolderFiltrationDecomposition`. This gives actual composition
series for every graded quotient of `s`, with counts summing to `m`.
`equivJordanHolderMultiplicityTransport` then transports each supplied
series along the corresponding graded representation equivalence.
The representation `τ` is unchanged, using its identity equivalence.

In the reverse direction, the proof transports the supplied composition
series of every `pieces i` back to the corresponding actual graded
quotient of `s`. It chooses their lengths and series, and applies
`jordanHolderFiltrationAdditivity`. That result lifts the actual
interval series into the ambient invariant-subspace lattice and
concatenates them, producing an actual composition series of `A`.
Its factor count is the sum of the supplied counts, hence `m`.

The two specializations use the fixed actual image filtrations
`T.normalizedRefinedOppositeJacquetFiltration` and
`T.normalizedComposedOppositeJacquetFiltration`. The theorem
`normalizedOppositeJacquetFiltrationGraded` supplies their same-index
graded equivalences to the corresponding normalized opposite Jacquet
representations of the original grades. Applying the helper therefore
proves both clauses of the target.

Every original index is retained, including repetitions and zero
grades. The helper imposes no positivity assumption on the length, so
empty filtrations use the empty sum. The functors, groups, and
normalization characters are unchanged; the composed action retains
both the outer and inner modulus factors. Smoothness is used by the
imported graded-comparison theorem. No admissibility, irreducibility,
finite-length certificate, splitting, exactness certificate or desired
comparison is supplied as an additional premise.

This is an internal derived proof using published finite-series
additivity, decomposition and transport together with ordinary
coinvariant exactness through the graded-comparison theorem. It claims
no separate literature theorem. It supplies the filtration-summation
adapter only: the constituentwise inequality, equal Weyl totals,
positivity and quotient criterion, and irreducible-head consequence of
the host comparison remain separate obligations.
