# Actual simple-root quotient transitions

This derived construction converts an actual field Borel-compatible comparison
to integer coordinate data, and determines the resulting actual quotient map.
It uses the published field root-datum comparison, canonical full lattice
realizations, and full fppf quotient cancellation.

`CoordinateRootDatum.fieldBase` transports a supplied coordinate root base to
the actual character and cocharacter lattices over a field. Its simple-root
support and positive-root predicate agree with the original ones.

`basedCoordinateIsoOfBorelCompatibleFieldIso` takes two connected reductive
groups over an arbitrary field, supplied coordinate split maximal tori,
realized full root data, actual compatible group and commutative-torus
isomorphisms, and fixed regular exponents sign-adapted to the two bases.
Equality of the full dynamic parabolics under transport is required.
The constructor derives a `BasedCoordinateIso`, including its all-test
monomial formula, rather than assuming a coordinate lattice comparison.
The original full lattices, including their central directions, are retained.

The proof realizes both coordinate data on their actual lattices, transports
the bases using preservation of integral root heights, and applies
`borelCompatibleRootDatumComparison`. It conjugates the resulting full
root-datum equivalence by the canonical lattice realizations. Its exact
character pullback formula gives the monomial identity on every relative
test scheme.

For a supplied `BasedCoordinateIso` over any scheme, full fppf source quotient,
compatible actual quotient map, and actual quotient charts which commute
with simple-root evaluation, `quotientChart_comp` and
`quotientChart_transition` identify that map with the induced simple-root
permutation. Cancellation is justified by the full fppf quotient predicate;
no injectivity on field-valued points is substituted for it.

This module does not construct a relative Borel atlas or perform effective
descent. Those remain obligations of the arbitrary-base Weil-presentation
theorem.
