# A common characteristic-polynomial parameter

This module supplies the invariant parameter used to localize concordance in the forward implication of Henniart–Lemaire (2011), II.2.9 and II.2.11. It is a derived construction for the Library's norm and association relation of I.1.2.

On the twisted side take the nonleading characteristic-polynomial coefficients of the cyclic norm. On the ordinary side take the same coefficients after base change to the cyclic algebra. Conjugation leaves the coefficients unchanged. The formula for the cyclic norm of a twisted conjugate reduces to ordinary conjugation because the power of the generator at the degree of the algebra is the identity. The association relation also identifies two matrices by conjugation, so associated elements have equal parameters.

The coefficient maps are continuous because each coefficient is a polynomial in the matrix entries. This is the same universal-polynomial argument used for field coefficients in `TransposeInvariantProof`, here over the commutative cyclic algebra. Base change and entrywise automorphisms are continuous on units by continuity on entries and on inverse entries. The finite norm product is then continuous.

Equality of the ordinary parameters implies equality of characteristic polynomials over the base field. The coefficient formula for base change and injectivity of the base field in the nonzero cyclic algebra recover each nonleading coefficient. The polynomials are monic of the same degree, so these coefficients determine them.
