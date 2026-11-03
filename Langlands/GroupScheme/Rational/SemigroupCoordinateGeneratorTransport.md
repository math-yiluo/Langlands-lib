# Coordinate and Lie bounds for semigroup generators

This internal derivation is conditional on the exact published
`AugmentationLieContainmentStatement` at arbitrary universe `u` and over any
field. For a semigroup generator and a supplied smooth connected affine
representative, `semigroupGeneratorAction` constructs the actual restricted
automorphic action from the generator's stability and the representing
inclusion. Equivariance of that action and support
transport through its monomorphic inclusion identify the intrinsic support
with the ambient support. The containment criterion then gives the same
semigroup bound on the representative's actual augmentation coordinates.

Conversely, if an already supplied smooth connected affine generated
representative has augmentation support in a given additive subsemigroup, the
criterion gives its intrinsic Lie support bound. The monomorphic inclusion
transports that support into the ambient group, and stability of the generated
envelope supplies stability of its actual represented range. The range is
therefore an admissible semigroup generator. All subgroup functors and
equivariance conditions use every test scheme; no zero character is adjoined.

This focused adapter does not prove the coordinate/Lie containment criterion or
the host semigroup commutator theorem. It supplies two internal transport steps
from the existing action-weight transport and represented-action constructions.
