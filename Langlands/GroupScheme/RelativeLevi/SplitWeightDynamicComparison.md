# Positive-weight terms and the actual contracting subgroup

This derived module compares a supplied regular root-height chart, equipped with
independent nonnegative root weights, to an actual dynamic contracting group.
The chart lies in a group `U` with a monomorphic homomorphism `j : U → G`.
Its factored roots must recover exactly the ambient root maps in the positive
list, and its natural weights must equal their pairings with the supplied
cocharacter. The ambient root maps are torus equivariant and belong to an open
split cell whose negative-list weights are nonpositive. An affine representative
`v : V → G` of the cocharacter's dynamic contracting functor is supplied.

`orderedProduct_mem_unipotent_of_supported` proves on every scheme test that a
root product supported on strictly positive weights contracts, using the existing
root-point contraction and subgroup closure. The supported coordinate theorem
is transported from spectra of rings to every affine test by the canonical
isomorphism with the spectrum of global sections.

`isRepresentedBy_positiveWeightInclusion` proves that the composite of the
chart's weight-cutoff-one inclusion with `j` represents precisely the supplied
cocharacter's dynamic contracting functor. The forward direction uses the
chart's coordinate-support characterization and the supported-product lemma.
For the reverse direction, the affine representative's universal point has a
supported coordinate vector. This vector gives a point of the chart's positive
weight term with the prescribed ambient composite. Precomposition with that
universal factorization proves equality on every scheme test. The argument
therefore proves an all-test functor equality, not just an affine- or fibrewise
comparison.

`positiveWeightDynamicIso` is the resulting group-scheme isomorphism to `V`;
its composite with `v` is exactly the original positive-term ambient inclusion.
`hasFiniteVectorBundleSeries_of_positiveWeights` transports the finite series
already constructed by `RootWeightData.hasFiniteVectorBundleSeries` across this
isomorphism. No new reductivity or root-existence theorem is asserted here; the
result assumes the stated actual chart and cell data. It does not establish
choice compatibility or descend the filtration. Provenance is the existing
root-point contraction, supported-coordinate, represented-subgroup and
root-weight-series constructions.
