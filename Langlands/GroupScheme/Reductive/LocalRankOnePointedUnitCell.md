# Pointed etale lifts with unit residue-cell coordinates

This internally derived application combines the actual centralizer field
unit-coordinate construction with prescribed-action pointed etale lifting.
It makes no new external-source correspondence claim.

`RingRootCell.PointedEtaleUnitCellData` records an actual residue point of a
supplied group, a pointed affine etale normalizer lift with its prescribed
torus action and exact recovery, and unit cell coordinates for the residue
point after left multiplication by the positive root at one.

`LocalRankOneCell.baseChangePointsEquiv_factorization` transports a supplied
cell factorization through the multiplicative pullback-point equivalence,
preserving the two root coordinates and transporting the middle torus point
by the standard split-torus comparison. Its generic statement keeps this
calculation independent of the specialized centralizer.

`pointedEtaleUnitCellReflection` first chooses the scalar and unit coordinates
on the actual residue-field centralizer. The actual pullback-point equivalence
carries both the normalizer transporter equation and the cell factorization
to the original base. An identity map of the residue spectrum identifies the
algebra-induced base map with the canonical residue map. The pointed etale
transporter construction then lifts exactly this chosen point through the
whole-base root-coroot reflection. No independently chosen scalars are identified.

The base ring is any commutative local ring. The ambient torus is supplied as
a closed fibrewise maximal split torus, with its root datum, actual opposite
root parametrizations and the stated two-root annihilator cocharacter.
The full Isomorphism Theorem and ring Weyl-data construction remain open.
