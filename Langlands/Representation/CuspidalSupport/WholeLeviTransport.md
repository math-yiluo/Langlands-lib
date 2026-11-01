# Cuspidality under arbitrary whole-Levi transport

This shared module retains the two cuspidality transport theorems originally
published in `Langlands.Representation.Exponents.PersistenceTransport`, with
their original names in `Langlands.CuspidalSupport`, statements and proofs. It
is imported by that module and by the cuspidal-product derivative quotient
support helper.

`isLeviQuasicuspidal_transport_of_conjugatesLevi` removes the minimality
restriction from the published whole-Levi transport theorem. The published
`minimalConjugatingCosets` theorem writes the given permutation as a minimal
conjugating permutation followed on the right by an element of the source
block Weyl group. The latter transport is inner and is intertwined with the
original representation by `transportWeylEquiv`. Quasicuspidality passes through
this equivalence and the minimal transport theorem. The transport composition
identity then returns the original permutation. Over a topological field,
`isLeviCuspidal_transport_of_conjugatesLevi` adds the existing admissibility
transport theorem. No irreducibility or positive rank assumption is needed.


The direct inputs are `MinimalConjugatingCosetsProof`, `AssociationReduction`
and `MinimalWeylTransportProof` in `Langlands.Representation.CuspidalSupport`.
Moving the two results here avoids duplicate proofs without importing exponent
persistence or `MaximalConeLifting` into the support helper. This is internal
algebraic infrastructure; it introduces no new mathematical assertion.
The field and representation-carrier universes remain independent.
