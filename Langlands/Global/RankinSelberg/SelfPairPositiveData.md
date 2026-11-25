# Nonzero spherical vectors and positive quotient measure for self-pairs

Internal helpers for the proof of `CuspidalSelfPairContinuationStatement`.

A genuine supplied cuspidal spectral presentation includes a restricted tensor
equivalence onto a nonzero finite slice. Its tensor exceptional set is contained
in its spectral exceptional set. Choose a nonzero vector in each exceptional
factor and form their elementary tensor, using the reference vectors elsewhere.
The elementary tensor is nonzero by finite tensor separation and injectivity of
the finite stage in the direct limit. At each place outside a larger exceptional
set the action fixes this tensor. The tensor equivalence, inclusion of the finite
slice and inverse of the full realization's finite-image equivalence carry it to
the required nonzero spherical vector.

The Library's cuspidal Whittaker expansion then shows that the Whittaker function
of every nonzero vector is nonzero somewhere. Otherwise every term of its
expansion vanishes, its cusp function is zero, and injectivity of the cusp-function
map forces the vector to be zero. This uses Cogdell (2004), Theorem 1.1, through
the imported Library proof.

The measure on the adelic Whittaker quotient has full support. The proof uses its
regularity, nonzeroness and right-translation invariance from the Library. A nonzero
regular measure has a compact set of nonzero mass. The right translates of a
nonempty open set cover that compact set, and a finite subcover shows that the
open set cannot have zero measure. This is an internal homogeneous-space argument
following the same proof as `QuotientIntegration.IsCompatible.isOpenPosMeasure`;
it is applied directly to the actual quotient and its fixed measure.

These helpers do not assert the continuation of a partial Euler product.

`SphericalWhittakerNonvanishingStatement` records their existence consequence:
for every supplied presentation and finite set containing its exceptional set,
and every standard additive character, there is a nonzero vector spherical outside
that set whose Whittaker function is nonzero somewhere.
`sphericalWhittakerNonvanishing` proves this proposition. Both universe parameters
of the presentation are retained. The full-support measure result is a separate
helper in the same module.
