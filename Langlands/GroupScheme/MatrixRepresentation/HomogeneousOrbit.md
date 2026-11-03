# Matrix-vector orbits through homogeneous scheme quotients

This internal construction connects the actual matrix-representation scheme
action in `MatrixRepresentation.SchemeAction` with the geometric descent and
constancy results in `SchemeActionHomogeneousConstancy`. It works for an
arbitrary field in universe `u`, an actual finite matrix representation of a
group scheme, a group homomorphism `i : B → G`, and an actual quotient scheme
morphism `q : G → Q`. The index of the representation is a small finite type,
as in the existing matrix-representation interface.

The required quotient data are flatness, surjectivity and quasi-compactness,
and the following implication on every relative scheme test: two group
points with equal images under `q` have their right quotient in the range
subgroup functor of `i`. No group structure on `Q` is assumed.

`isFixed_constant_of_restrict` turns the existing all-test fixed-vector
predicate for the restricted representation into fixedness of the constant
affine-space point under the restricted categorical action. Coordinate
injectivity, the matrix action formula and naturality of scalar coordinates
prove this comparison for every test and refinement.

`coefficientHomogeneousOrbitMap` is the actual affine-space-valued morphism
on `Q` obtained from that fixed point by homogeneous orbit descent.
`quotient_comp_coefficientHomogeneousOrbitMap` identifies its pullback along
`q` with the original orbit morphism. Its provenance is the actual
`descendedHomogeneousOrbitMap`, rather than a stipulated map or a map on
rational points alone.

If the field is algebraically closed, `G` is connected and reduced, and `Q`
is proper over the field, `isFixedVector_of_proper_homogeneousQuotient` shows
that the original vector is fixed by `G` on every scheme test. This follows
from proper homogeneous quotient fixedness for the affine coefficient space,
followed by the fixed-vector equivalence in `MatrixRepresentation.SchemeAction`.
The geometric theorem derives connectedness and reducedness of `Q` from the
faithfully flat surjection, so they are not additional inputs here.

For a specified coordinate vector, an exact all-test coordinate-line
stabilizer condition identifies a second group homomorphism's range with
the points acting by some unit scalar on that vector.
`range_eq_top_of_fixed_coordinateVector` proves that range is the whole
group functor whenever the vector is fixed by `G`: on every test the unit
scalar `1` witnesses membership. Pointwise extensionality proves equality.
`range_eq_top_of_proper_homogeneousQuotient` combines this with the preceding
constancy result. The subgroup defining the quotient can differ from the
line stabilizer.

These are derived internal constructions and consequences of the named
action, descent and constancy interfaces. Properness of any Borel quotient,
triviality of its line character, and the exact Borel normalizer theorem
remain separate obligations.
