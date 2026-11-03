# Image transport for actual semigroup subgroup functors

This is derived infrastructure for the equivariant functoriality discussed
in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
printed p.111 / PDF p.137, after Example 3.3.7. It uses actual group schemes,
all-test equivariance, and actual coordinate pullback. The conditional
Lie-support theorem retains `AugmentationLieContainmentStatement` as a
premise; this module does not yet prove the full comparison statement.

`GeneratedImage.factorGroupHom` constructs the group homomorphism from the
source group into any representative of its closed image envelope. Its
underlying map equals the existing scheme factor. The two maps agree after
the monomorphic inclusion, which proves their equality.

`factorGroupHom_isDominant` proves that a dominant positive power map into
the envelope makes this homomorphism dominant: the power factors as the
source group multiplication followed by the homomorphism. The proof works
for every power, without requiring separability.

`CoordinateWeights.support_subset_of_dominant` uses reducedness of the target
and actual affine dominance to obtain injectivity of coordinate pullback.
An equivariant nonzero augmentation eigenfunction then stays nonzero with
the same character. `RelativeRoot.actionWeightSupport_subset_of_dominant`
uses the explicitly assumed coordinate/Lie containment criterion on both
smooth connected groups to transfer a Lie-support semigroup bound. Smoothness
over the field supplies the reducedness needed for injective pullback. The
semigroup may be empty or contain zero, and no restriction on characteristic
or injectivity of the differential is introduced.
