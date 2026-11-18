# Polynomial presentations for zero or one Laurent coordinate

`firstPolynomialMap` evaluates a complex polynomial at the Laurent monomial
with exponent one in the unique first-block coordinate and zero in the
complement. Identifying the first block with the integers takes this map to
the ordinary inclusion of polynomials into Laurent polynomials followed by
inclusion into the product Laurent algebra.

`exists_coprime_firstPolynomial_fraction` starts with a fraction of Laurent
polynomials supported on the first block. It multiplies both Laurent
polynomials by a common monomial to obtain polynomials. The monomial is a unit
and cancels in the fraction. The polynomial fraction gives an element of
`RatFunc ℂ`, which maps into the product fraction field through the injective
polynomial coordinate map. Its reduced numerator and denominator supply the
coprime presentation, with a nonzero denominator as a polynomial.

`exists_constant_of_firstBlock_fraction` treats a block of rank zero. Its
Laurent algebra is the complex coefficient field, and the inclusion takes
each coefficient to the corresponding constant in the product ring.

These derived presentations convert Laurent-block descent into the polynomial
form used for unit-circle pole removal.
