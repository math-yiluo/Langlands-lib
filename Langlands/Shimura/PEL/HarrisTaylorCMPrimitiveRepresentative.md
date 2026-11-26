# Primitive polarization representatives on the same Harris family

Use a `TateNormalizedCMRepresentative` at a fixed original Harris level
over a connected admissible base and an algebraically closed point. The
Harris arithmetic, signature charts, base, Weil transition, adelic and
torsion data are those of this representative.
`tateNormalizedCMPrimitiveRepresentative` selects an actual homomorphism
to the given dual on the same abelian scheme with the predicate
`HarrisPrimitivePolarization`. The original polarization is a positive
integer multiple of this primitive map. A normalized frame from the
original orbit lets `harrisPrimitivePolarizationOf` construct the map,
and `harrisPrimitivePolarization_unique` determines it on that family.

For an actual isomorphism of the abelian schemes, the polarization
transport uses `DualWitness.transportMap`.
`tateNormalizedCMPrimitiveRepresentative_transport` identifies the
primitive homomorphisms under this transport from the original integral
cross-multiple equation. `harrisPrimitivePolarization_pullback` uses the
proved `polarizationRayPositivity`, and the determinant and dimension
condition on the original representative supplies the prescribed positive
relative dimension.

Conversely, `tateNormalizedCMPrimitiveRepresentative_originalMultiple`
recovers an integral cross-multiple equation between the original
polarizations from equality of the transported primitive homomorphisms.
If the original polarizations are `k • mu` and `l • mu'`, then additivity
of the dual transport by `DualWitness.transportMap_nsmul` gives the
transported second polarization as `l • mu`. The equality of the
two maps multiplied by `l` and `k` respectively gives the original
integral cross-multiple data with scalar `l / k` in `ℚˣ`.
