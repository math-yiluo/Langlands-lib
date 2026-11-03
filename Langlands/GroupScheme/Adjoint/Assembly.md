# Actual finite centre and elementary adjoint quotient assembly

Author: Worker 1350.

This internal derived unit constructs an explicit finite closed representative
when the full centre is trivial, and supplies elementary bridges for the actual
full-centre quotient construction. It introduces no external structural theorem
and does not prove unconditional quotient existence.

For any group scheme over any base scheme, the full all-test centre is normal:
a central point commutes with the conjugating point over the same test scheme,
so conjugation fixes it. Hence the range of every actual scheme-theoretic centre
representative is normal. This uses the entire published `center` functor and
places no smoothness or reducedness condition on the centre.

The actual unit homomorphism `kernelUnit G` from the trivial group scheme has
range equal to the bottom subgroup functor. Every point of the trivial group
scheme is the unique map to the tensor unit. In a separated group scheme the
unit section is a closed immersion, by the proved closed-immersion cancellation
for its composite with the structure map. Consequently, when the full centre
is bottom, that unit is an actual closed representative of the centre. Its
structure map is the identity of the base and is finite.
`finiteCenterOfCenterEqBot` returns this actual group scheme and inclusion in a
dependent pair, together with their closed-centre and finiteness proofs. Its
underlying group scheme is exactly `Grp.trivial (Over S)` and its inclusion is
exactly `kernelUnit G`; the construction uses no choice of representative.
Forgetting this explicit data proves that a separated group scheme with trivial
full centre satisfies `HasFiniteCenter` without any representability premise.
Connected reductivity includes an affine structure
map and hence supplies separatedness, so connected reductivity together with
trivial full centre implies the exact published `IsAdjoint` predicate.

For a group-scheme homomorphism with separated target, the published
`kernelι_isClosedImmersion` instance makes the actual kernel a closed subgroup.
Equality of its range with the full centre therefore supplies the entire
`IsSchemeTheoreticCenter (kernelι q)` predicate.

Finally `isAdjointQuotient_of_fppf_kernel_range` combines those bridges with the
scheme and group descent proved in `Langlands.GroupScheme.Adjoint.QuotientDescent`.
Over every field, it consumes connected reductivity of both source and target,
trivial full centre of the target, the flat, surjective and locally finitely
presented underlying quotient map, and equality of the actual kernel range
with the full centre of the source. It supplies every field of
`IsAdjointQuotient`, including both universal properties for arbitrary targets
in the same universe. Quotient existence and its structural properties remain
separate obligations.

All provenance is internal: the implemented proofs use the published group
object, subgroup functor, centre and kernel constructions, elementary group
identities, the published descent assembler and pinned Mathlib's proved affine,
separated and finite morphism properties. No statement is introduced as an
unproved premise or a new axiom.

The range and closedness facts for the identity subgroup are reused from [UnitSubgroup](../UnitSubgroup.md).
