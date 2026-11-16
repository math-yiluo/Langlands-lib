# Field unit cell coordinates and affine unit restrictions

This internally derived prerequisite combines the existing field rank-one cell
calculus with the ring cell data and elementary scheme unit loci. It makes no
new correspondence claim to external literature.

`RingRootCell.CellData.toFieldCellData` copies the actual group schemes, root
maps, torus map, weight, equivariance and open-cell immersion from ring cell
data over a field into the field calculus. `field_gpt_eq` verifies that the
two scalar-point conventions agree by comparing their single coordinate.

`RingRootCell.CellData.exists_unitFieldCellCoordinates` assumes cell data
over a field, an actual cocharacter whose composite with the weight is twice
the identity, the integral lattice pairing equal to two, a supplied reflection
normalizer whose square is in the torus, and irreducibility of the ambient
group. It supplies a decomposition of `xp(1) n` into negative-root, torus and
positive-root factors, with both scalar coordinates global units on the field
spectrum. The proof packages the supplied data into the published field
`RankOneRootCellRelation.WeylData`. The lattice and ring reflections agree
because their morphisms are both `1 - alpha followed by h`. The published
field decomposition and its two unit-coordinate theorems then apply; the
scalar-point comparison translates their conclusions back to the ring calculus.
All the listed geometric and normalizer hypotheses remain supplied inputs.

`LocalRankOneUnitCell.isUnit_appTop_of_range_subset_basicOpen` works for any
scheme morphism and global function: containment of the morphism's image in
the function's basic open implies the pulled-back function is a unit. The
proof uses the preimage formula for basic opens and the structure sheaf's
germwise unit criterion.

`LocalRankOneUnitCell.AffineUnitRestrictionData` records an actual affine
scheme mapping by an open immersion into a supplied scheme, a lift of a
supplied field point with exact composite, and invertibility of the pullbacks
of two supplied global functions. `affineUnitRestriction` constructs these
data when both functions pull back to units at that field point. The basic
opens of the two functions contain the image of the point. Choose an affine
open inside their intersection; the singleton spectrum of the field factors
through that affine open. Pullback to this neighbourhood makes both functions
units by the preceding unit-locus criterion. No condition on the ambient
scheme, including reducedness or noetherianity, is needed.

This contribution does not apply the field decomposition to the actual relative
centralizer or shrink the previously constructed pointed etale normalizer to
its cell locus. It does not construct `RingRootCell.WeylData` over a ring or
prove the unchanged local Isomorphism Theorem. Those applications remain.
