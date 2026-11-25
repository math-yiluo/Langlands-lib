# The actual rank-one relation extracted from a negative-simple translation

This is an internal specialization of the simple-wall construction and
the comparison of zero-weight middle factors in
`SimpleWallCellDecomposition`. All coefficient rings and relative scheme
tests are allowed, including nonreduced ones.

For a finite reduced coordinate root datum `P`, a base `b`, a simple root
`a`, enumerations of the negative and positive roots, and selected positions
for `-a` and `a`, `cellRankOnePart` retains precisely those two coordinates
and the original torus coordinate of a cell point. It is the actual
ambient-group point
`u_-a(v) * i(t) * u_a(w)`. The definition needs neither parametrization
nor sign hypotheses.

`cellLeviPart_simpleWall_eq` assumes the explicit compatibility
`P.toLinearMap x y = coPairing x y` of the root datum pairing with the
coordinate dot product. The simple-wall cocharacter has zero pairing
exactly at the opposite pair `a, -a`. Since each root enumeration is
injective, its zero-weight ordered product has just the selected factor.
Applying `rootProductZeroPart_eq_single` on each side of the torus proves
that the middle factor is exactly `cellRankOnePart`.

`cellRankOnePart_mul_negativeSimple_of_cell_relation` additionally assumes
an affine ambient group and actual root parametrizations for every root.
For any relative scheme test `Z`, any two cell points `x, y`, and any
global function `c` on `Z`, an equality
`cell(x) * u_-a(c) = cell(y)` implies
`rankOne(x) * u_-a(c) = rankOne(y)`.
The torus coordinates on the two sides are the original coordinates of
`x` and `y`. No local-ring, field, reducedness, smoothness or cell-openness
hypothesis is used in this assertion.

The proof checks that all negative and positive roots have respectively
nonpositive and nonnegative simple-wall weights. The translating root
point has weight zero, so it lies in the dynamic centralizer.
`cellLeviPart_mul_of_cell_relation` then extracts the equality of middle
factors. The preceding single-factor formula identifies both middle
factors with the stated rank-one products. Thus the proof uses actual
dynamic subgroup membership and all-test equalities, without detecting
equalities by field points.

This module reduces a full cell relation to a rank-one relation. It does
not prove equality of the torus coordinates after the coroot
quotient, a rank-one Bruhat formula, or the relative derived-group
existence statement.
