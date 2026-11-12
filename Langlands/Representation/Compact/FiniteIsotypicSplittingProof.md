# Finite compact-isotypic block decomposition

Worker 141 proves
`finiteIsotypicSplitting : FiniteIsotypicSplittingStatement`, Renard IV.1.7's
second display, printed page 95 / PDF page 101 of the registered French 2026
edition. The page and the IV.1.5–IV.1.6 context were read.

For the finite set `S` of compact irreducible classes, sum their actual intrinsic
projectors to obtain `P`. Published orthogonality and idempotence prove that `P`
is idempotent and that every selected component absorbs `P` on either side.
Use the family indexed by `Option S`: at `some c` take the class projector,
and at `none` take `id - P`. This entire family is orthogonal, idempotent and
sums to identity, including when `S` is empty.

The derived `projectorRangeCofanIsColimit` constructs the actual coproduct of
its range subrepresentations, with the original representation as vertex. The
range at `some c` is an object of the published isotypic predicate. The range
at `none` is killed by every selected projector; the already proved
`avoidingPart_iff_blockProjector_zero` therefore excludes all selected
irreducible subquotients, not only subrepresentations.

Naturality gives both Hom-vanishing directions between the avoiding part and
each selected isotypic part. Distinct selected isotypic parts have zero Hom by
their projector orthogonality. These are all unequal `Option S` index cases,
and together with the actual coproduct establish the precise published
category-decomposition predicate.

The published target and imported files remain unchanged. The group and carrier
universes `u v` stay independent and no extra premise is added.
