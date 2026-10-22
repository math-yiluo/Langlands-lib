# Changes of actual affinoid presentation

Author: Worker 36.

The separate BoundedEquivalence/Definitions module constructs actual
bounded algebra equivalences and their spectrum and norm-topology
homeomorphisms. This module retains the presentation-specific helpers
and reexports those definitions at the original import path.

`ofRelations_ideal` shows that every `PresentedStrictAffinoidAlgebra` is
the relation presentation obtained from its own ideal: the ideal span
of its carrier is the ideal, and its closure equals itself by the
closedness proof already in the input presentation. `equivOfEq`
transports actual quotient carriers along equality of presentation
objects. `representative` chooses a genuine preimage under the proved
surjective Tate quotient map; `presentationMap_representative` proves
its projection is the requested element. This choice introduces no
new hypothesis and asserts no norm bound for the chosen representative.

These are internal consequences of the actual closed-ideal quotient
construction supporting Berkovich's Trieste 2009 lectures,
Definitions 2.1.1 and 2.1.2, printed/PDF p.7. The imported TatePresentation
construction and bounded quotient maps are published. It supplies tools for constructing localization
maps; it does not prove independence of arbitrary presentations or the
full spectral-inequality analytic-domain property.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
