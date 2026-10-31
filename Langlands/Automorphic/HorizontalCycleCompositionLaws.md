# Composition of actual horizontal cycle transport

Author: Worker 2.

This internal API uses the existing actual horizontal cycle representations and
full operator transport in `HorizontalCohomologyTransport`. The number field
`F : Type u` has arbitrary universe, the natural rank `n` is positive, coefficients
are complex in actual operator realization spaces, and the natural degree `q`
may be zero. The cycle carrier remains the kernel of the actual horizontal
differential, inside cochains equivariant for the full standard infinite compact
group. The endpoint representations retain their existing finite adelic action.

Two typed proof abbreviations express composition, with `A` applied first:

- `Intertwiner.horizontalCyclesMap_comp_apply` states that transporting a cycle
  by the full operator composite `B.comp A` equals transporting first by `A` and
  then by `B`.
- `Intertwiner.horizontalCyclesMap_comp` states the corresponding equality of
  bundled finite adelic intertwiners between the actual cycle representations.

The pointwise proof removes the cycle and horizontal-cochain subtype wrappers,
uses alternating-map extensionality and closes at each reduced Lie tuple by
reflexivity of coefficient composition. The bundled proof applies intertwiner
and linear-map extensionality and then the pointwise formula. Both declarations
contain complete proof terms of explicit equalities. No additional compatibility
equation or transport datum is an input, and no simplifier attribute is installed.

The five explicitly named local additive groups on the underlying function spaces
and the three on realization spaces are canonical `Submodule.addCommGroup`
structures. Provenance is internal: the formulas follow from the existing cycle
restriction and coefficient postcomposition constructors in
`HorizontalCohomologyTransport` and `HorizontalTransportCore`. No new
identification with external literature is asserted.

This unit concerns cycle transport. Quotient representative/projection formulas,
quotient identity/composition and actual equivalence specialization remain
separate. It supplies no smoothness, topology, finiteness, nonvanishing,
coefficient attachment or analytic/sheaf comparison theorem.
