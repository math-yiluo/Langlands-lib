# Positive actual-series multiplicities from nonzero simple maps

This module proves the internal derived proposition
`Langlands.JordanHolderSimpleMapDetectionStatement`. It treats arbitrary
fields and monoids, with five independent universes for the field, monoid,
ambient representation `A`, subobject or quotient representation `B`, and
irreducible test representation `τ`.

The implemented helper `positive_of_simple_map` starts with an actual-series
multiplicity witness for `B` and the actual self-count one of the irreducible
`τ` from `irreducibleMultiplicity`. If the supplied nonzero map has source
`τ`, Schur's injectivity alternative makes it injective. The existing
`jordanHolderInjectiveMonotonicity` then gives `1 ≤ m`. If the supplied
nonzero map has target `τ`, Schur's surjectivity alternative makes it
surjective, and `jordanHolderSurjectiveMonotonicity` gives the same
inequality. Thus either direction of the nonzero map implies `0 < m`.

For the subobject clause the proof constructs the actual quotient of `A` by
the range of the supplied injection `i : B → A`. The quotient projection
is surjective and its kernel is exactly the range of `i`.
`jordanHolderShortExactDecomposition` applied to this actual short exact
sequence and the ambient count `M` provides actual-series counts `m` and
`c` for `B` and the quotient, with `m + c = M`. The helper makes `m`
positive, and the sum gives `m ≤ M`.

For the quotient clause the proof constructs the actual kernel of the
supplied surjection `q : A → B`, with its actual injective inclusion into
`A`. The same short-exact decomposition supplies counts `a` and `m`
with `a + m = M`; the helper again proves positivity and the sum proves
the upper bound.

`jordanHolderSimpleMapDetection` is exactly the conjunction of these two
clauses. Every multiplicity conclusion retains the actual composition
series in `HasJordanHolderMultiplicity`. There is no chosen
semisimplification, numerical-length replacement, or assumption that a
nonzero map alone forces finite length. The finite-series witness for `B`
comes from the supplied ambient finite-series witness.

The argument is an internal algebraic derivation from the Library's
irreducible self-count and actual short-exact multiplicity results. Its
project import closure consists only of generic representation filtration
definitions, transport, refinement, comparison, and length proofs. It
imports no GL, induction, Jacquet, segment, multisegment, tempered, square
integrable, regular, or analytic classification module. It therefore does
not use any downstream conclusion excluded by the segment existence task.
The result remains conditional on the actual ambient map, ambient count,
irreducibility, and nonzero simple map; it proves no group-specific
existence assertion.
