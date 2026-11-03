# Solvable semigroup intersections

This internal application treats smooth affine groups over an arbitrary field
and the actual all-test subgroup functors. The semigroup intersection conclusion
retains `SemigroupRealizationStatement` and
`Torus.SolvableFixedContainmentConnectedStatement` as explicit premises. No proof
of either premise or of the full comparison conjunction is claimed here.

The whole-torus fixed subgroup is stable because the acting torus is
commutative. Its tangent submodule is the intrinsic zero weight space: the
published fixed-tangent comparison identifies it with the all-algebra
differential invariants, and evaluation of the zero character is one. A split
torus is isomorphic to a diagonalizable group with a finite free character
lattice. The published closed representability and diagonalizable smoothness
theorems therefore give a smooth closed fixed-subgroup representative.
`fixedSubgroupSmoothRepresentative` chooses such a group scheme, and
`fixedSubgroupSmoothInclusion` is its actual homomorphism to the ambient group.
The accompanying properties theorem proves representation of the all-test
fixed subgroup, closedness of this inclusion, and smoothness over the field.
These choices do not assert connectedness.

Assume the independent general solvable connectedness criterion, and suppose
the ambient group is connected and satisfies `IsSolvableScheme` on all tests.
Applying the criterion to the fixed subgroup itself proves that its
representative is connected. If \(0\in A\), its zero-weight tangent space lies in the
full selected weight span. The published split-torus support bound makes it an
actual semigroup generator, and hence it lies in `semigroupSubgroup c A`.

For an equivariant closed inclusion \(j:H\to G\), the published
closed-inclusion functoriality puts this fixed subgroup in the inverse image of
the ambient semigroup subgroup. The shared intersection geometry, conditional
on realization, supplies a smooth closed representative of this inverse image.
Equivariance preserves stability. The general solvable connectedness criterion
then makes this representative connected. The shared exact-Lie uniqueness
argument gives
`(semigroupSubgroup b A).comap j = semigroupSubgroup c A`.

This proves the zero-containing part of the solvable alternative, still
conditional on the two named premises. The zero-excluded and normal
alternatives are separate. The argument is an application of the independently
stated CGP connectedness prerequisite; its consumer proofs use the Library
interfaces just described and add no geometric axiom.
