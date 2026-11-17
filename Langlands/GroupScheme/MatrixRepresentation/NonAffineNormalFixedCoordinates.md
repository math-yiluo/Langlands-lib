# Fixed coordinates of normal subgroups without affineness

This derived module extends the published normal fixed-coordinate argument
to arbitrary group schemes over a field `k` in universe `u`.
There is no affine, smooth, connected or finite-type hypothesis on either
group scheme.

`section_eq_of_affine_tests` detects equality of global sections of an arbitrary
relative scheme by pullback to every relative affine test. It encodes sections
as points of the affine line, applies the published affine-test morphism
extensionality theorem `OrbitLimit.hom_ext_of_algebraSpec`, and recovers equality
of coordinates. `isFixedVector_of_affine_tests` applies this to each matrix-vector
coordinate and uses point-matrix naturality. Thus fixedness on all affine
tests implies the published fixedness predicate on all scheme tests.

`normal_fixed_coefficient_of_affine_tests` proves that each ground-field linear
coefficient of an affine translate of a vector fixed by a normal subgroup is
again fixed by that subgroup. For an arbitrary affine subgroup point, it extends
both points to the tensor product of their test algebras and applies the
published `normal_fixed_affine`. The published `fixed_tensor_coefficients`
extracts the coefficient equation. The preceding affine-test criterion then
gives fixedness on every scheme test. This replaces the single global affine
model of the subgroup used in `normal_fixed_coefficient`.

`normal_fixed_coordinates_of_affine_tests` takes matrices `B` and `C` whose
columns are subgroup-fixed and whose composite `B * C` fixes every subgroup-fixed
vector. Linear functionals and the preceding coefficient theorem establish the
coordinate stability equation on each affine group point. Pullback naturality
and the section equality criterion extend it to every relative scheme test,
which is exactly the existing `IsStableCoordinates` predicate.

Finally, `normalFixedCoordinates` constructs the actual group-scheme
representation on the supplied coordinates by `restrictCoordinates`, also
assuming `C * B = 1`. Its source is the original group scheme. All inputs are
published Library constructions; this module adds the affine-cover argument
needed to remove the global affine models from the earlier proof.
