# Torus-unit fixation under equivariant realizations

This internal composition transfers the published
`IsFixedByScalarTorusUnits` predicate between spaces carrying the same
scalar-extended rational-point action. An equivariant map preserves fixation;
an injective equivariant map reflects it. The proof applies the map to the
fixation equality or reflects that equality by injectivity. It retains the
original torus inclusion, character-valuation kernel and group action.

`TorusUnitFixationTransportStatement` packages the equivalence for every
injective equivariant map. Its theorem `torusUnitFixationTransport` applies the
two directions just proved. The field, scalar extension and valuation are
arbitrary; the two action spaces may have different universes.

The concrete building specialization uses the published
`conjugateReducedBuildingEquiv`, its injectivity and
`conjugateReducedBuildingEquiv_smul` from
`ConjugateApartmentRealization`. This equivalence rebases the transported
quotient so that the ambient inner twist cancels, and is equivariant for the
same original rational-point group. Torus-unit fixation is therefore equivalent
on the reference quotient and its realization in the original quotient.

The maximal-unramified predicate is the scalar predicate specialized to its
canonical valuation, so this transport applies to it without another premise.
These internal lemmas prove no existence of reference tori, Galois stability,
or equivariance for the coefficient action. Those remain separate inputs.
