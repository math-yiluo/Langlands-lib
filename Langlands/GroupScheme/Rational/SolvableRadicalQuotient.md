# Quotients by represented solvable radicals

This internal supporting result derives quotient properties from the Library
predicate `IsSolvableRadical`. It does not assert existence of a radical.

`HasTrivialSolvableRadical G` means that every smooth connected solvable normal
closed subgroup of `G` has trivial image on every test scheme. It is the
solvable analogue of the existing `HasTrivialUnipotentRadical` predicate.

The inverse image of a smooth connected solvable normal closed subgroup under
an affine fppf quotient by a represented solvable radical is again closed and
normal. The full kernel is identified with the radical, so the quotient map is
smooth and has geometrically connected fibres. The inverse image is therefore
smooth and connected. Its point groups are solvable because their kernel embeds
in an image of the radical point group and their quotient embeds in the supplied
solvable subgroup's point group.

Radical maximality places this inverse image in the full kernel. Faithfully flat
descent then makes the original subgroup trivial on every test scheme. The
ground-field unipotent-radical consequence uses solvability of point groups of
unipotent groups. Applying it after base change to the algebraic closure proves
connected reductivity of an affine fppf quotient by a geometric solvable radical
over an arbitrary field.

The main interfaces are
`IsSolvableRadical.hasTrivialSolvableRadical_quotient`,
`IsGeometricSolvableRadical.hasTrivialGeometricSolvableRadical_quotient`, and
`IsGeometricSolvableRadical.isConnectedReductive_quotient`.
The affine target and source are explicit hypotheses. Quotient reductivity also
requires the ambient source to be smooth and connected. No perfectness,
characteristic, or splitting hypothesis is imposed.

These are derived results from the existing radical maximality, kernel
comparison, quotient smoothness, connected-kernel, solvability, and fppf
base-change interfaces. No additional structural theorem is assumed.
