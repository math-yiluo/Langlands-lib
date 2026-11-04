# Unipotent bounds from dominant orbits in pseudo-reductive groups

Authors: Worker 1549, Worker 1547, and Worker 317.

This internal prerequisite works over an algebraically closed field in universe
`u`, in every characteristic. It derives the unipotent dominant-orbit and
homogeneous-curve bounds from pseudo-reductivity and a solvable closed
stabilizer. The actual quotient, its exact all-test fibers, its smooth
surjective quasi-compact quotient map, and its curve dimension remain supplied.

`SchemeAction.range_eq_bot_of_unipotent_kernel` applies to any homomorphism
from a smooth connected affine unipotent group into the ambient group. If its
all-test image lies in the full action kernel and a rational section has a
solvable closed represented stabilizer, its image is trivial on every scheme
test. The proof forms its smooth connected normal closure. The closure factors
closedly through the stabilizer and is solvable. The proved
`SmoothConnectedNormalClosure.range_eq_bot_of_isSolvable_of_isPseudoReductive`
then gives the conclusion using the actual diagonal-kernel embedding.

`SchemeAction.unipotent_dimension_le_one_of_dominant_orbit` takes smooth
connected affine unipotent groups `H` and `U`, a monomorphic map `U → G`,
a closed inclusion `H → U`, and the actual Lie dimension bound
`Lie.dimension U ≤ Lie.dimension H + 1`. The supplied section is fixed by
`H`, and its `U` orbit map is dominant and quasi-compact. The acted-on scheme
is reduced, separated, and locally of finite type over the field. The proved
codimension-one normality makes `H` normal in `U`; the dominant-orbit theorem
puts its image in the full ambient action kernel. The preceding range theorem
kills it. Monicity reflects triviality to `H → U`, so the actual Lie dimension
of `H` is zero and that of `U` is at most one.

`HomogeneousQuotient.unipotent_dimension_le_one` specializes this argument to
the identity coset of a supplied smooth exact homogeneous quotient curve by
a solvable closed subgroup `B`. Its unipotent `U` is not contained in `B`,
while the composite image of `H` is contained in `B`. Noncontainment gives a
moving rational point, and the actual quotient curve gives the dominant
quasi-compact orbit.

`curveUnipotentDataOfPseudoReductive` constructs the actual smooth connected
affine group representing the dynamic unipotent subgroup for a cocharacter
of a split torus mapping into `B`. It takes noncontainment of that dynamic
subgroup in `B`. The supplied smooth quotient makes `B` smooth; the canonical
dynamic constructions give the two actual unipotent groups in `G` and `B`
and their closed inclusion. The exact quotient dimension formula and the
signed dynamic dimension formula give their Lie dimension gap at most one.
The preceding orbit bound supplies the dimension at most one recorded in the
constructed `CurveUnipotentData`, alongside its actual moving orbit.
`positive_roots_eq_of_noncontained_unipotent_on_curve` applies the intrinsic
dynamic tangent comparison and disjoint root-weight subspaces to conclude
equality of any two positive actual relative roots for the cocharacter.

The proofs adapt the existing Library orbit and dynamic-curve constructions,
using the new normal-closure unipotence theorem in place of their structural
torus premise. Worker 317 proposed the original normality and action-kernel
route; Worker 1547 implemented the existing stabilizer and curve constructions;
Worker 1549 supplied the diagonal-kernel step and these consumers. This is
derived internal content. The host positive-root uniqueness statement, actual
quotient existence, the curve dimension bound, and the required dynamic
noncontainment remain separate obligations.
