# One-entry symmetric tuples recover the original relation

This derived helper supplies the first chart in the symmetric tuple
construction of Stacks Lemma 68.8.3, Tag 0BBN, registered as
`stacks-stratification-2026-11-02` (`0BBN.html`, proof). The tuple parameter
is one less than the number of entries, so parameter zero corresponds to
the original one-entry chart. The equivalence relation has separated
source. The symmetric quotient declarations also assume affine object
and relation schemes. All constructions use an arbitrary universe `u`.

`tupleDistinctOpen_zero` proves that the distinctness open is the entire
one-entry tuple scheme: there are no two different indices in `Fin 1`.
`tupleDistinctZeroIso` identifies its open scheme with the object scheme
using equality with the top open. Its `hom` formula identifies the map
with the zeroth coordinate. Its `inv_projection` and `projection_inv`
formulas state the two inverse identities.

`tupleSymmetricZeroProjection` descends the unique coordinate through
the symmetric quotient. Every permutation of `Fin 1` fixes that coordinate.
`tupleSymmetricMap_zeroProjection` is the defining descent identity.
`tupleSymmetricZeroIso` has this projection as its forward map and the
ordered one-entry inverse followed by the quotient map as its inverse.
The quotient universal property proves one inverse identity, and the
ordered inverse identity proves the other.
`tupleSymmetricMap_zeroIso_hom` records the forward-map formula.

`tupleSymmetricCrossZeroProjection` descends the original ordered
relation-arrow map through the two symmetric groups. Their product is
trivial for one-entry tuples, so invariance follows from the identity
action. `tupleSymmetricCrossMap_zeroProjection` is its descent formula.
The `t` and `s` formulas identify the two original endpoints with the
symmetric endpoints followed by `tupleSymmetricZeroIso.hom`; quotient
uniqueness and the ordered endpoint identities prove them.

`tupleSymmetricCrossZeroSection` constructs a symmetric correspondence
from an original relation arrow by lifting its two endpoints to ordered
one-entry tuples and then taking the quotient. Its `projection` formula
is the first inverse identity.
`tupleSymmetricCrossZeroIso` packages both maps as an isomorphism. For
the remaining inverse identity, the proof checks the two ordered
endpoints and then applies uniqueness of descent through the quotient.

These are identifications of actual schemes and their endpoint maps.
The module supplies the one-entry chart; it does not prove the full
Noetherian first-level theorem.
