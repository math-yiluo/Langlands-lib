# The unitary lattice field-transport relabelling identity

For p-adic fields `F` and `E` in independent universes, an algebra isomorphism
`f : F.Carrier ≃ₐ[Padic p] E.Carrier`, and a unitary virtual supercuspidal class
`y` over `E`, `unitaryLatticeEquiv_eq_equivMapDomain` identifies
`unitaryLatticeEquiv F E f y` with the finite-support relabelling
`Finsupp.equivMapDomain (unitaryBasisEquiv F E f) y`. The proof is `rfl` and
retains the independent representation-carrier universe.

This internal identity was first proved, in identical form, in
`HenniartCompositeFactorCentral` and in `UnitaryPairFactorTransport`. Those
identical identities are consolidated here, next to the reused field-transport
constructions. Both
central-character and pair-factor modules import this shared declaration.
No new mathematical assertion is introduced by the relocation.
