# Actual representatives in the uniform triple input

This internal contribution proves
`uniformRepeatedTripleTransfer_iff_canonical`: the uniform local proposition
with arbitrary supplied supercuspidal representatives is equivalent to the
two seed moves for the literal patterns `(νB,B,B)` and `(νB,B,νB)`. The local
representation-theoretic seed moves remain unproved.

`uniformTripleTensorIso` applies the existing external tensor functor to the
three supplied smooth isomorphisms. Its family of isomorphisms is constructed
with the finite dependent recursor, in the same rank family as
`threeBlockSmoothFamily`. `uniformTripleOccurrence_iff_of_isos` retains the
presenting invariant subrepresentation and its invariant submodule, and
composes the isomorphism from the tensor to their actual quotient with the
tensor isomorphism or its inverse. The ambient smooth object is unchanged.

`RepeatedTripleSeedTransfer` asks for `(A,B,B) → (B,A,B)` and
`(A,B,A) → (A,A,B)` or `(B,A,A)`, assuming `[A] = ν[B]`. The theorem
`uniformRepeatedTripleTransfer_of_seed` obtains a supercuspidal isomorphism
from `[C] = [B]` or `[C] = [A]`, forgets it to the smooth category, and applies
the tensor occurrence equivalence before and after the seed move. This
recovers the supplied actual representative `C` in every output.

`nuSupercuspidal` is the existing actual supercuspidal twist by
`T.determinantPowerCharacter d 1`, with its published open-kernel and
determinant-kernel certificates. Its class is definitionally
`T.supercuspidalClassRealPowerTwist d 1 B.isoClass`.
`CanonicalRepeatedTripleSeedTransfer` asks for the two seed moves with
`A` literally this actual twist of `B`. If `[A] = ν[B]`, equality of
supercuspidal classes gives an actual isomorphism to that twist, so
`repeatedTripleSeedTransfer_of_canonical` transports both copies of `A`
where needed and proves the preceding seed interface. Conversely, the
uniform proposition specializes directly to the canonical objects and
reflexive class equalities. These constructions prove the stated equivalence.

Every seed hypothesis concerns an actual irreducible, admissible,
finite-length smooth representation of `GL_(d + (d + d))`, for positive `d`.
All occurrences use the normalized upper Jacquet functor at
`threeBlocks d d d`. The supplied field, topology and determinant normalization
are retained, the field and carrier universes remain independent, and no
unitary or cuspidal-line reduction is assumed.

The provenance is internal functoriality, quotient representatives and
isomorphism transport. No printed source is invoked to establish either
seed move. The import closure consists of the existing uniform interface,
its definition-level smooth tensor, twist and Jacquet dependencies, and this
module. The added proofs use only the actual external tensor functor,
composition of smooth isomorphisms, the quotient definition of
supercuspidal classes, and the actual twist constructor. No excluded
classification conclusion is used.
