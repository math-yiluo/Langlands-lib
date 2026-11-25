# Local reflection of original scalar compatibility

This internal adapter for the finite vector-bundle filtrations of supplied
relative radicals defines the scalar operation on the original
group points prescribed by an actual module point chart. Agreement of the
operations for two charts gives scalar-linearity of their actual section
transition.

For lifted point charts, the operation is natural under arbitrary scheme-test
maps, with the prescribed canonical comparisons for composite lifts. The
canonical fixed-lift module normalization retains this same original point
operation. Independence from the lift therefore gives `HasLinearTransitions`,
the input for the constructed actual module descent datum. Equality of these
original point operations can be checked on any open cover of any test.

`scalarIndependent_of_specComponents` reduces independence on all schemes to
literal affine spectrum tests whose two original lifts factor through two
members of any prescribed open cover of the covering scheme. The proof
successively pulls the cover back by the first and second lifts, then takes
the affine basis cover of the resulting tests. It uses the actual component
maps and pullback equations to retain the factorizations. No nonempty overlap,
constant rank or affineness of the original test is required.

The provenance is derived from actual point-chart naturality, semilinearity of
actual section pullback, linearity of canonical module comparisons and the
joint faithfulness of an actual scheme open cover. Quotient-specific scalar
agreement on local affine component restrictions remains a consumer obligation.
