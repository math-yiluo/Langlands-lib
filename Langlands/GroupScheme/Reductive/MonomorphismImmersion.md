# Immersions from a closed regular torus image

This internal construction composes the dynamic immersion criterion with
arbitrary-base representability and the relative regular-centralizer comparison.
It does not assert the host closed-immersion theorem.

For a monomorphism `f : H → G` between smooth affine group schemes over any
scheme, with geometrically connected source, the first theorem assumes a
supplied representative `i : K → H` of a dynamic centralizer and closedness of
`i ≫ f`. General-base dynamic representability supplies the two source unipotent
subgroups, the two target unipotent subgroups and the target centralizer. The
restriction of `f` to the supplied centralizer composes with the closed target
centralizer inclusion to `i ≫ f`, so that restriction is a closed immersion.
`Dynamic.isImmersion_of_isClosedSubgroup_centralizer` then gives the immersion
of `f`. No choices of dynamic representatives are premises of the new theorem.

`AffineRegularBorel.regularCocharacter` is the actual coordinate cocharacter
obtained from `CoordinateRootDatum.regularExponent`. The reductive specialization
works over an arbitrary commutative ring. Its source has a monic coordinate
torus map, assumed fibrewise maximal, and a supplied full common fibrewise root
datum. The datum makes its root index finite. The chosen exponent is regular
on every root, so `AffineRegularBorel.centralizer_eq_range_of_mono` identifies its entire
all-test dynamic centralizer with the torus image. Reductivity provides
smoothness and geometric connectedness. Applying the first theorem proves that
a monomorphism to a smooth affine group is an immersion, under the explicit
premise that the composite torus map is a closed subgroup.

The provenance is internal: all mathematical inputs are imported Library
results, and the implemented proofs are their composition. In particular,
closedness of the torus image, descent from local splittings, smoothness or
affineness of an arbitrary target, and global closedness of `f` are not proved
here. No noetherian assumption is used.
