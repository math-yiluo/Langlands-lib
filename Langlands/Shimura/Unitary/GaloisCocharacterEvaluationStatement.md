# Galois evaluation of Harris cocharacters

`CentralSimpleUnitaryData.ComplexCocharacterGaloisEvaluation` is a proposition
about the actual rational group scheme attached to central simple unitary data D.
It quantifies over every Q-algebra automorphism s of C, every group-scheme
cocharacter χ of the iterated real-to-complex base change, and every unit u of C.
Its two clauses state the same compatibility in two existing point models.

The first clause states that evaluation of `D.galoisCocharacter s χ` at u is
`D.complexPointGaloisAction s` applied to evaluation of χ at the unit obtained
by applying the inverse automorphism s inverse to u. Both sides are actual
C-valued points of the rational group scheme, expressed as morphisms over
Spec Q. Thus the automorphism is inverse on the input and forward on the output.

The second clause identifies that evaluated transported point in the
scalar-extended algebra similitude group through `D.rationalAffinePointsEquiv`.
It is the coefficient automorphism s applied to the coordinates of evaluation
of χ at s inverse of u. The existing `AlgebraInvolution.coefficientAut` changes
the algebra coefficients by s tensor identity and the common similitude
multiplier by s. This clause specifies the whole group element, not only its
multiplier.

This is an internal compatibility target for the existing constructions in
`GaloisCocharacterPoints`, `GaloisCocharacters`, and `GaloisPoints`. It introduces
no new literature convention, signature restriction, chart, or descent datum.
The definitions of transport, evaluation, and coordinates are fixed imported
constructions; the proposition assumes none of the asserted equalities.
This file states the target and supplies no proof. It does not assert equality
of scheme morphisms from equality on complex points, matrix-chart transport,
or the identification of a reflex stabilizer.
