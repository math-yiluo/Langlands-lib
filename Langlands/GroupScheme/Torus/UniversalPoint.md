# Universal points of split tori

This internal construction gives a universal point of the actual split torus
`splitTorus (Spec R) I` over the group algebra `R[I → ℤ]`. Its unit coordinates
are the monomials with exponent vectors `Pi.single i 1`. Every point over any
commutative `R`-algebra is the image of this point under evaluation at its unit
coordinates.

The construction uses the published finite-product torus and its actual affine
point identification. `algebraPointsEquiv_naturality` transports the published
naturality for each multiplicative-group factor. `exponentValue` multiplies
integer powers of a family of units; `evaluateUnits` extends this monoid map
by the group-algebra universal property. The theorem
`universalPoint_evaluateUnits` follows by checking each coordinate monomial.

The motivating source is Milne, *Algebraic Groups* (2017), 12.12, printed
pp.234–235 (PDF250–251), whose proof uses monomial coefficients for
representations of diagonalizable groups. This arbitrary-base universal point
and its named algebra maps are derived implementation infrastructure. The file
does not assert weight decomposition or a base-change theorem for Lie algebras.
