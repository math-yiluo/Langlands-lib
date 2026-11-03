# Conditional fixedness for proper actions with invariant affine neighborhoods

Worker 1460.

This internal assembly retains two explicit global hypotheses:
`UnipotentAffineOrbitClosedStatement` (Kostant–Rosenlicht for actual affine
scheme-action orbit images) and `SolvableProperFixedPointStatement` (a rational
fixed point for a connected smooth affine solvable group acting on a nonempty
proper scheme). It does not prove either input.

`isSolvableGroupScheme_of_isUnipotent` applies the published solvability of
all test-scheme point groups of an affine locally finite type unipotent group
to the test obtained from the algebraic closure of the ground field. The
base-change points equivalence identifies this group with the group in the
definition of geometric solvability. This lemma works over any field.

`HasFixedPointInOrbitClosures` is a proposition for an actual action over an
algebraically closed field. For every rational section `x`, it requires an
all-test fixed rational section `y` whose underlying point belongs to the
closure of the actual orbit morphism's image.

`hasFixedPointInOrbitClosures_of_solvableProperFixedPoint` constructs the
reduced closed orbit-closure subscheme and its all-test equivariant action.
The closed immersion into the proper ambient scheme makes this subscheme
proper. The orbit contains the image of the identity section of the group,
so the subscheme is nonempty. The supplied proper solvable fixed-point theorem
gives a fixed rational section of the subscheme. Its composite with the
equivariant closed immersion is all-test fixed in the ambient scheme, and
its underlying point belongs to the orbit closure by the immersion's range
formula.

The final theorem,
`isFixed_of_invariantAffineNeighborhoods_of_geometric_inputs`, assumes a
smooth connected affine unipotent group acting on a proper scheme over an
algebraically closed field, with an invariant affine open neighborhood for
every rational section. Unipotence supplies geometric solvability, and the
previous lemma supplies a fixed point in each orbit closure. The conditional
affine-neighborhood argument then proves that every rational section is fixed
on every test scheme. The ambient scheme need not be reduced.

Provenance is internal: the module composes the actual reduced orbit-closure
construction, unipotent point-group solvability, the base-change points
equivalence, and the affine-neighborhood argument. Its geometric existence
and closedness inputs remain explicit hypotheses.
