# Actual subgroup data for the parabolic-orbit comparison

Author: Worker 76.

This internal bridge uses the published block Levi projection, its section,
the literal six decomposability theorem, and the canonical diagonal projection
on a decomposable intersection. It applies over every commutative ring and in
every rank, including zero. It imposes no minimality condition on the permutation.

The actual orbit stabilizer is the subgroup of the target parabolic consisting
of elements whose inverse conjugates lie in the source parabolic.
`parabolicOrbitStages` is the inverse image of the intersection parabolic in
the target Levi. It contains the target radical and the orbit stabilizer.
Pulling either subgroup back along the target Levi section gives exactly the
target intersection parabolic. In particular that section lands in the
stabilizer on the subgroup required for induction in stages.

The stabilizer containment uses the first clause of
`blockParabolic_sixDecomposable` and
`blockIntersection_leviProjection_mem`. All other assertions follow from the
section law and the definitions of inverse conjugation and subgroup inverse
image.

The coefficient homomorphism on the stabilizer is inverse conjugation followed
by the source Levi projection. On the intersection with the target radical it
takes values in `sourceUnipotent F B C w`; this uses the sixth literal
decomposability condition. The resulting homomorphism
`parabolicOrbitRadicalToSource` is surjective with the explicit group
homomorphism `parabolicOrbitRadicalSourceSection` as a right inverse. The
section conjugates the embedded source element into the target radical.
Both maps are continuous for a topological ring, and the stabilizer, stages
subgroup and radical intersection are closed for a Hausdorff topological ring.
These assertions use the actual matrix and subgroup topologies.

These are internal group identifications for the proof of the local
normalized comparison, motivated by Bernstein–Zelevinsky (1977), sections
5.16–5.17 and 6.4, rather than separate claims of a comparison isomorphism.
No integration, quotient equivalence or normalized comparison is asserted here.
