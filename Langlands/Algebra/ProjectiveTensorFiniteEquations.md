# Finite coefficient equations for projective tensor factors

This internal algebraic unit derives finite generation of coefficient ideals
from projectivity. The right tensor factor need not be finitely generated.
A finite set of tensors has a finitely generated ideal of all contractions
against linear forms on the right factor.

For one tensor, split the projective module into a free module. The image of
the tensor has finitely many nonzero free coordinates. Those coordinates
generate its full coefficient ideal. The quotient by that finite ideal kills
the tensor in the free module and hence in the original projective summand.
Conversely, each chosen coordinate is a contraction against a linear form on
the original module. Finite unions give sums of coefficient ideals, proving
the finite-set assertion. HasFiniteCoefficientIdeal records finite generation
of the resulting ideal as a predicate on a set of tensor equations.

Two finite-equation consequences use algebra structure on the right tensor
factor. The coefficient ideal of the image of a finitely generated ideal
under an algebra map is finitely generated. Quotienting the coefficient
algebra by the coefficients of the images of finitely many ideal generators
kills the full ideal. Likewise, the coefficient ideal of all differences of
two algebra maps from a finite-type algebra is finitely generated: equality
after this quotient is checked on finitely many algebra generators. These
arguments apply to arbitrary commutative base rings and projective right
algebras, without a noetherian hypothesis.
