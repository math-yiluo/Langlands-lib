# Borel averaging onto the specified smooth complex standard module

The normalized inducing character on the actual upper triangular
subgroup is the product of the existing `borelFactor` values on the
diagonal. The position weights and exponents are those of the supplied
complex parameter list with the principal series modulus shift.
The proof identifies its value with the Library's
`principalSeriesCharacter` of the same list.

For a Borel left Haar measure and the second-countable topology on
the upper triangular subgroup, the inverse-argument weighted Borel
average defines a complex-linear map from compactly supported smooth
matrix tests on the units to `complexStandardModule`. The averaged
section is smooth by the Borel averaging theorem and inversion.
Evaluation on a diagonal times a unipotent matrix uses the inducing
law and the specified diagonal character.

Every smooth section of the specified standard module has the same
inducing law on the whole Borel by triangular coordinates. The
surjectivity theorem for Borel averaging then gives a test mapping
to that section. This is an internal link between the matrix test
space and the smooth coefficient module.
