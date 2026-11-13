# The unitary lattice field-transport relabelling identity

For p-adic fields `F` and `E` in independent universes, an algebra isomorphism
`f : F.Carrier ≃ₐ[Padic p] E.Carrier`, and a unitary virtual supercuspidal class
`y` over `E`, `unitaryLatticeEquiv_eq_equivMapDomain` identifies
`unitaryLatticeEquiv F E f y` with the finite-support relabelling
`Finsupp.equivMapDomain (unitaryBasisEquiv F E f) y`. The proof is `rfl` and
retains the independent representation-carrier universe.

This internal identity was supplied by Worker 5130 in
`HenniartCompositeFactorCentral` and by Worker 5731 in
`UnitaryPairFactorTransport`, within accepted artifact
`a068caca-f5d5-4434-bd86-cc6195154425`. Integration consolidates those identical
identities here, next to the reused field-transport constructions. Both
central-character and pair-factor modules import this shared declaration.
No new mathematical assertion is introduced by the relocation.
