# Geometry and dimensions of subgroup-product orbits

Worker 1556. This is an internal derivation from the imported product,
fixed-vector, smooth-dimension, and closed-orbit interfaces. It supplies helpers
for the finite-field product criterion and does not prove envelope normality.

`isUnipotent_tensor` proves that the actual binary product of two affine
unipotent groups over an arbitrary field is unipotent. The common-fixed-vector
theorem applies to the two product inclusions because the first inclusion is
normal on every relative scheme test. Every product point is the product of its
two included coordinates, so the common nonzero vector is fixed by the entire
product on every test, including nonreduced tests.

For a smooth connected affine group, `smoothOfRelativeDimension_lie_dimension`
identifies its actual Lie dimension with the constant smooth relative dimension
supplied by the Library's smooth connected dimension theorem. Pullback and
composition of these dimensions prove `lie_dimension_tensor`: the Lie dimension
of the actual product is the sum of the two factor dimensions. This lemma takes
an affine structure-map instance for the product as well as smooth, affine,
connected factors. The same pullback rule proves `lie_dimension_baseChange` for
any morphism between field spectra in the given universe; the original group is
smooth, affine and connected, and the base-changed group has an affine structure
map. Neither formula inserts a numerical dimension assumption.

Over an algebraically closed field, `isClosed_range_orbitMap` applies the
published Kostant–Rosenlicht theorem `unipotentAffineOrbitClosed` to the actual
product action constructed in `SubgroupProductOrbit`. Both factors are smooth,
affine and unipotent, and the ambient scheme is affine and locally of finite
type. Product unipotence supplies the acting group's required hypothesis.
`unipotentClosedOrbitQuotient` then constructs the actual orbit-image homogeneous
quotient by the diagonal copy of the scheme-theoretic intersection, assuming the
second subgroup embedding is closed and the intersection is smooth. Its fibers
are the all-test cosets already proved in `SubgroupProductOrbit`; its projection
is smooth, surjective and quasi-compact through the imported quotient API.

The orbit need not be the whole ambient group in this result. Establishing that
conclusion from finite-field rational-point surjectivity, and descending the
resulting product geometry, remain obligations of the separate product proof.
