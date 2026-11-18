# Actual finite Galois stages of continuous unit cohomology

For a Galois extension `S/K`, an open normal subgroup of the Krull group
has a finite Galois fixed field `E`. This gives `galoisFixedStage`. The
quotient of the Krull group is identified with `Gal(E/K)` by restriction.
Units of `S` fixed by the subgroup are the units of `E`, with inclusion
into `S` as the inverse to that identification. The quotient cohomology
therefore agrees with the ordinary relative cohomology of `E/K`.

`finiteStageToContinuous_eq_relativeToContinuous` checks that the group
map in the finite-stage comparison is restriction to `E`, and its
coefficient map is inclusion of units. This identifies the finite-stage
comparison with actual relative inflation on cohomology. The published
finite-stage exhaustion theorem then shows that every continuous class
comes from an ordinary class over some finite Galois intermediate field.
This applies in particular when `S` is a separable closure of any field.

The construction implements the passage to a separable closure in
J.-P. Serre, *Local Fields* (1979), Chapter X, §5, printed p. 159 via
Mathlib's continuous-cochain complex.
