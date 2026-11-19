# Transport of continuous field-unit cohomology

For algebraic extensions \(S/K\) and \(T/E\), a commutative square of
field isomorphisms \(K\simeq E\) and \(S\simeq T\) transports the
actual automorphisms by conjugation. Conjugation and its inverse are
continuous for the Krull topologies. The upper field isomorphism
transports units equivariantly and both unit maps are continuous for
their discrete topologies.

`unitCohomologyIsoOfRingEquiv` applies the resulting cochain
identification to continuous cohomology. The Lean construction uses
the Library's continuity theorem for conjugation and the cohomology
isomorphism for simultaneous group and coefficient transport. This
allows continuous unit cohomology to be computed in either of two
compatible choices of separable closures. The intended use is the
transport of absolute corestriction in Serre, *Local Fields* (1979),
Chapter XI, §§1–2, pp. 166–168, between common and chosen closures.
