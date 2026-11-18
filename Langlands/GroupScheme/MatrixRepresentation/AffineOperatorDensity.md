# Scalar commutants and full operator algebras

This internal proof development concerns part (b) of Milne, *Algebraic Groups*
(2017), Proposition 4.19, pp. 90–91 (registered source
`milne-2017-algebraic-groups`).

For the operator algebra of an actual affine representation, every module
endomorphism is an actual self-intertwiner: write its ground-field restriction
as a matrix and use its commutation with the generating universal coefficients.
The scalar-intertwiner hypothesis therefore makes every module endomorphism
scalar. This is `endomorphism_scalar`; it does not require irreducibility.

For `operatorAlgebra_eq_top`, the actual representation is also assumed to be
irreducible. The stability comparison then makes the coordinate space a simple
module for the operator algebra. With this simple-module hypothesis and scalar
module endomorphisms, Jacobson density, applied simultaneously to a finite
ground-field basis, shows that the generated operator algebra is the entire
endomorphism algebra.

`HasScalarIntertwiners` names the actual scalar-commutant condition. Both results
work over arbitrary fields and do not assume reducedness of the affine group
scheme. Scalar extension itself is proved in a subsequent module.
