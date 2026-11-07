# Actual duals of centered unitary segment parameters

This is an internal construction from the published strong-head duality,
cuspidal duality and admissible unitary duality theorems. It adds no
classification hypothesis or new external representation-theoretic assertion.
The canonical or supplied topology is retained throughout, with independent
field and carrier universes.

For a segment `Δ` of length `l`, `dual_midpoint_base` identifies the midpoint
base of `Δ.dual` with the cuspidal dual of the midpoint base of `Δ`. The dual
segment begins at the dual of the last member of `Δ`. Cuspidal duality negates
the twist exponent, and composing the midpoint twist leaves exponent
`-(l - 1)/2` on the dual of the original base. Positivity of `l` justifies the
natural subtraction conversion used in this calculation.

`SquareIntegrableSegmentParameter.contragredient` constructs a parameter on
the actual smooth contragredient of the supplied action. Its segment is
`d.segment.dual`; its degree equality is the original equality; its chosen
base is `CuspidalProductContragredient.dualRep T d.base`, whose underlying
action is the actual smooth contragredient of the original midpoint base.
The midpoint identity and `dualRep_represents` prove its base certificate.
The admissibility of the original supercuspidal base and compact-open
cofinality imply that this dual base is unitarizable.

The strong-head witness is `d.head.contragredient`. A private equality
elimination lemma commutes smooth duality with the stored degree transport,
so the witness concerns the original supplied action's smooth dual. The
displayed segment and base identities are definitional. This construction
does not assert a new square-integrability theorem for arbitrary actions: it
transports precisely the fields of the supplied parameter structure.
