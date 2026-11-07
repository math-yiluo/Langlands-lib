# Character spaces detected by separating linear coefficients

This is an internal linear-algebra comparison for the actual universal character
spaces of `MatrixRepresentation`. It does not assert existence of a representation,
a coordinate function, a coefficient family, or its equivariance.

`coefficientExtension` extends a supplied linear map from the original finite
coordinate space to a family of scalars over an arbitrary algebra. Its formula
uses the images of the standard basis vectors. `HasCharacterCoefficients` says
that this extension intertwines the universal representation matrix with the
diagonal action of a supplied family of actual rational characters. Injectivity
is a separate hypothesis in the conclusions that require separating coefficients.

For a character vector, each nonzero coefficient forces equality of its assigned
character with the vector's character. The proof cancels the image of a nonzero
field scalar, which is a unit even in a coordinate ring with zero divisors or
nilpotents, and then uses injectivity of actual character units. Thus every
nonzero character space occurs among the assigned coefficient characters.
Restricting the coefficients to a finite set containing all indices assigned a
specified character gives an injective linear map from its character space and
the stated dimension bound. A unique possible coefficient bounds the dimension
by one; a separately supplied occurrence hypothesis gives dimension exactly one.

The motivation is comparison of restricted covariant functions with polynomial
coefficients on a supplied product cell. The results here are derived directly
from the published universal-character equation and elementary linear algebra;
they do not claim that the necessary geometric coefficient equivariance has
already been established.
