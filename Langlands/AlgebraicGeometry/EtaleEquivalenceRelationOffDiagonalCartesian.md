# Nonidentity arrows in cartesian diagrams

This internal, derived infrastructure addresses the affineness condition in the
open-extension step of Stacks Project Proposition 70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`. It uses the existing scheme pushout,
unit-complement decomposition, finite-tail recovery, and the cofiltered affine
limit theorem. All schemes are in arbitrary universe `u`. It asserts no
Noetherian approximation result.

In `EtaleEquivalenceRelation.IsCartesianHom`, `unit_isPullback` proves that the
unit square of any cartesian relation morphism is a scheme pullback. A compatible
arrow mapping to a unit must be its own source unit: the source pullback supplies
uniqueness. This supplies both the required lift and its prescribed object map.
`unit_opensRange_preimage` applies the open-immersion image/preimage formula to
this square. When both source maps are separated, `offDiagonalOpen_preimage`
takes complements to identify the inverse image of the nonidentity-arrow open.
`offDiagonalMap` restricts the actual arrow map to these opens;
`offDiagonalMap_ι` gives its inclusion equation, and
`offDiagonalMap_isPullback` is the inverse-image open square.

In `OpenExtension`, `arrows_isAffine_of_offDiagonal` transfers affineness across
`arrowsCoprodIso`. It needs only an affine ambient scheme and affine old
nonidentity arrows; the old whole arrow scheme need not be affine.
`offDiagonal_isAffine_of_extension` proves the reverse useful implication. The
nonidentity arrows are a closed coproduct summand of the extension: its range is
the complement of the other, open summand. A closed subscheme of an affine
scheme is affine.

`CartesianDiagram.OffDiagonal.diagram` restricts every actual relation arrow
map to its nonidentity-arrow open. Its identity and composition laws follow by
cancelling the monic open inclusions. `inclusion` is its natural transformation
to the relation diagram, and `cone` is the corresponding cone from the
nonidentity arrows of the supplied relation cone. The inclusion equations and
the original cone equations prove naturality. `isLimit` uses the proved open
pullback squares and connectedness of the cofiltered index to restrict the
relation limit, which itself follows from the supplied object limit.

`map_isAffine` first pulls affineness of an object transition back to the
relation transition using its cartesian source square, then restricts that
transition using the open pullback square. `exists_isAffine` applies Mathlib's
cofiltered affine-limit descent to this actual diagram. Its compactness and
quasi-separatedness assumptions are on the old arrow schemes; the unit
complements inherit them as closed subschemes. `isAffine_of_map` pulls an affine
nonidentity-arrow level back along any affine transition.

Finally, `tupleTailNextRelation_source_isSeparated` pulls separation back along
the actual invariant-open source square. For `p < N + 1`,
`tupleTailNextRelation_offDiagonal_isAffine` uses the recovery isomorphism to
make the extension arrow scheme affine (the whole finite tail is affine), then
applies `offDiagonal_isAffine_of_extension`. Thus the old invariant threshold
restriction has affine nonidentity arrows even if its unit component is a
non-affine quasi-compact open. This is the actual finite-tail input needed for
later affine-limit descent; no affineness of the entire restricted relation is
assumed.
