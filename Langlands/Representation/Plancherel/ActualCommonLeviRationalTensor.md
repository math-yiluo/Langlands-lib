# Rationality of the particular actual normalized compact tensor

This internal algebraic specialization implements the rationality step behind
Waldspurger, *La formule de Plancherel pour les groupes p-adiques*, V.3 formula
(1), printed p.295 / PDF p.61. It depends on the constructed actual generic
comparison and its proved fixed compact square.

Parameter inversion preserves the full evaluation-generated regular algebra by
the published `unramifiedRegularInversion`. Applying it to the coefficients of
a finite expansion proves polynomial inversion; applying it to the one
operator denominator proves rational inversion. Multiplication by an explicit
regular scalar ratio uses the product of its denominator and the existing
whole-operator denominator, before choosing an input vector.

`ScalarInverseData` retains an actual forward continued standard operator on the
smooth contragredient, its regularity at each inverse generic parameter, two
actual scalar-composition identities with the reverse dual continuation, and a
scalar represented by a nonzero regular numerator and denominator there.
These are explicit analytic helper inputs, not proved existence assertions.
No generic or tempered induced irreducibility is assumed.

The proved two-sided inverse from `ActualCommonLeviCompactTensor` is the inverse
of the actual compact reverse standard operator. Its injectivity and the
reverse-forward scalar composition identify this inverse with the reciprocal
scalar times the actual forward dual continuation. The other composition is
retained explicitly in the helper data. This supplies a rational inverse of
that particular operator; it does not assert rationality of arbitrary inverses.

Restricting the actual forward continuation and the inverse-parameter forward
dual continuation to the genuine generic locus, multiplying by the displayed
reciprocal scalar ratio, and tensoring proves `compactComparison_rational`.
The resulting denominator is one regular function for the entire tensor
operator. Combined with the previous unit's square, this identifies the
rational family with the actual forward/inverse-reverse-dual tensor on the
actual product-induced coefficient fibers.

Nonemptiness and density of that generic locus, continuation existence, scalar
composition existence and extension across individual factor poles at unitary
parameters remain separate closed targets. None is inferred by restricting to
a denominator nonzero set. Compact probability normalization, source formal
degrees and coefficient forms are unchanged.
