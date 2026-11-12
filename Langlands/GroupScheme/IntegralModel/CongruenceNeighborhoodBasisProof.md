# Actual integral-model congruence neighborhood bases

Author: Worker 99.

This proof establishes the published target
`Langlands.GroupScheme.LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement`
by the theorem
`Langlands.GroupScheme.LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof`.
It applies in arbitrary universe `u` to every nonarchimedean local field of
either characteristic and every supplied affine, flat, finite-type integral
group model. The integral-point image and the positive congruence images are
compact and open in the named rational-point topology; the congruence images
are normal in the integral image and cofinal in the ambient identity
neighborhoods.

The proof is an internal deduction from the published model and point-topology
interfaces and Mathlib's compact-ring and Krull-intersection theorems. It
introduces no additional literature assertion or structural group hypothesis.
In particular, it requires no smoothness, reductivity, connectedness, building
or special-stabilizer data.

The coordinate lemmas compare the original sections after the actual quotient
base change. Two reductions agree precisely when their original coordinate
values differ by an element of the corresponding maximal ideal power.
Algebra generators suffice for this equality. Krull intersection over a
Noetherian local ring shows that all positive reductions separate sections.

Continuity of the coordinate evaluations and finite generation express each
kernel as a finite intersection of open conditions in powers of the actual
maximal ideal. Expressing the same kernel with all coordinates proves it
closed, since ideals in a compact Hausdorff Noetherian ring are closed.
The compactness of the original section space then makes the kernels compact.
Their continuous images under the original `integralPointMap` are the
constructed `congruenceSubgroupAt`, so those images are compact.

The original integral-point map is injective, hence a closed embedding from
the compact section space into the Hausdorff rational-point space. The
published openness of its full integral image makes this embedding an open
map. It therefore carries the open congruence kernels to open sets in the
full ambient rational-point group.

For cofinality, choose an open identity neighborhood inside a given
neighborhood and pull it back to the section space. Its complement is
compact. Krull intersection shows that the intersection of all positive
kernels consists only of the identity, so it misses this complement.
Compactness for the directed family of closed kernels then gives a single
positive kernel disjoint from the complement, and its original generic image
lies in the given ambient neighborhood. The final theorem specializes the
compact-base results to the actual valuation integer ring and reuses the
published compactness, openness and normality results.
