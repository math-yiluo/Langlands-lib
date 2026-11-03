# Cover descent coherence on field components with isomorphic projections

This module constructs an actual compatible source descent datum from a
supplied simply connected central cover over an arbitrary field in universe
`u`. The target datum, finite decompositions of the actual double and triple
overlaps into spectra of fields, and isomorphism properties of their specified
projections to the original field spectrum are inputs.

For two specified isomorphisms of field spectra, the published full cover
transport and cover comparison give an actual source isomorphism lifting a
specified target isomorphism. Its exact equation is retained. Uniqueness
among all homomorphism lifts follows from the transported first universal
property and semisimplicity and centrality on the second side.

On each double-overlap component, apply that construction at its two
projections. On each triple-overlap component, apply the uniqueness result
only at its first and third projections and the specified transported target
isomorphism. `ComponentCoverLifts` assembles the component isomorphisms and
uses this uniqueness to prove the source cocycle.

This is an internal deduction from the named Library interfaces. It does
not prove the existence of the supplied cover, the field-component
decompositions or their projection isomorphisms, or effective descent.
It introduces no field-only predicate on a nonfield overlap.
