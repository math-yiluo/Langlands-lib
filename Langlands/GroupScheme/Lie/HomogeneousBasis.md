# Homogeneous finite bases of actual split-torus Lie actions

This is an internal construction from the existing actual differential weight
spaces and their proved split-torus internal direct-sum decomposition. The field
`k : Type u`, its characteristic, and the universe `u` are arbitrary. The target
group scheme `G` is affine over `Spec k`; an actual group scheme `H` acts on it,
and `j` maps an actual split torus `T` into `H`.

`HomogeneousLieBasis b j` stores a natural-number dimension, a basis of the
actual base-field Lie kernel indexed by that finite dimension, and an actual
character of `T` for each basis vector. Its `mem_weight` law states membership
in the existing `b.lieWeightSpace j`, whose eigenvector condition quantifies over
every commutative test algebra and every torus point. Zero weights and repeated
characters are allowed.

`Lie.FiniteCoordinates.homogeneousBasis` constructs this datum from any natural
finite coordinates on the actual Lie kernel and the split-torus hypothesis.
The coordinates over the base field show that the ambient Lie module is
finite-dimensional. Choose a finite basis of each character weight space, and
apply `AutomorphicAction.isInternal_lieWeightSpace_of_finiteCoordinates` and
`DirectSum.IsInternal.collectedBasis` to obtain a basis indexed by the disjoint
union of the component basis indices. Because the ambient module is
finite-dimensional, this disjoint union is finite. Reindex it by the standard
finite type, keeping the character attached to each index. The collected-basis
membership theorem gives the required weight law.

`HomogeneousLieBasis.differential_basis` extends this chosen basis to every
coefficient algebra using `Lie.FiniteCoordinates.baseChangeBasis`. The formula
for that extension identifies its vectors with actual coefficient changes of
the base-field basis vectors. Their defining weight-space membership gives the
character eigenvector equation for the original action's differential over that
algebra. The result includes the zero-dimensional Lie module and empty basis.

This unit supplies actual homogeneous Lie bases. It does not construct new
all-test vector-group coordinates, identify semigroup subgroup functors, or
prove the full ordered semigroup product proposition.
