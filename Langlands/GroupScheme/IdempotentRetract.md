# Actual closed retracts of idempotent group-scheme maps

Worker 632, for the relative normal-idempotent gluing input proposed by
Worker 47.

For an idempotent endomorphism of a separated group scheme over any base,
`idempotentRetract` constructs an actual closed subgroup with an inclusion
and a projection. Their composite is the original endomorphism; the reverse
composite is the identity of the subgroup. The subgroup agrees both with
the fixed subgroup of the endomorphism and with its full pointwise image,
on every relative test scheme.

The closed fixed-subgroup representation is the existing scheme equalizer.
Idempotence factors the original map through that subgroup. Its inclusion
is fixed by the endomorphism; monicity of the inclusion proves the
retraction identity. The factorization and fixedness identify the two
pointwise ranges.

A closed retract of an affine group is affine. If the original group is
also smooth, the existing arbitrary-base affine retract smoothness theorem
gives smoothness of this same subgroup. A scheme retraction is surjective
on underlying points, so it preserves connectedness; pulling the maps back
to every field-valued base point gives geometric connectedness as well.
No noetherian or reducedness hypothesis is used.

This is an internal construction from the published fixed-subgroup,
represented-subgroup factorization and affine retract geometry interfaces.
It makes no normality, simplicity, or classification assertion.
