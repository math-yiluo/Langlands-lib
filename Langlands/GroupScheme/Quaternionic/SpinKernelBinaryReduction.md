# Kernel generation from the binary spin subgroup

This internal module transports the published all-test binary kernel reduction
into the coefficient-algebra `KernelGenerator` used by `SpinKernelAssembly`.
It assumes the degree-two norm-one simple-connectedness statement explicitly.
It also assumes monomorphy of `BinarySpinLift.diagonalSpin` and inclusion of the
full spin-kernel range in the binary `productHom` range. Neither geometric
assumption is proved here.

`affineRootCoordinates` transports square roots of one through the inverse of
`Corepresented.affineSectionsAlgEquiv`, from a coefficient algebra to the global
sections of its relative spectrum. The comparison is an isomorphism for every
commutative coefficient algebra, without reducedness or characteristic limits.
`normOnePointsEquiv_normOnePoint` uses `LeviScheme.pointsEquiv_affine` and the
norm-one inclusion to identify the actual norm-one coordinates. The scalar
norm-one comparison follows from `normCoverScalarUnits_map`.

`diagonalSpin_affineRoot_points` substitutes those comparisons and
`gm_pointsEquiv_gmPoint` into `BinarySpinLift.diagonalSpin_root_points`, identifying
the resulting affine point with `kernelPoint`. `kernelGenerator_binary` applies
`BinarySpinLift.existsUnique_root_of_kernel` and transports its unique root back
through `affineRootCoordinates`.

Finally `kernelGenerator_of_binary` compares any supplied Levi lifts with the
constructed binary lifts by `IsLeviLift.unique`. Connected reductivity of the
norm-one source follows from the explicit simple-connectedness premise. The
binary lifts satisfy `IsLeviLift` by `isLeviLift_binarySpinLift`.

The provenance is internal. The module reuses Worker 5398's shared
`SpinLeviLift` comparison module unchanged, with its explicit conditional
simple-connectedness premise, and Worker 179's cancellation and uniqueness
module. This is a reduction toward the target, not a proof of
`SpinKernelGeneratorStatement`.
