# Additive-group divided-power operators

This module derives divided-power operators from an actual matrix
representation of the one-dimensional vector group. Let \(k\) be any field,
let \(n\) be a finite type with decidable equality, and let
\[
 \rho:\mathbb G_a\longrightarrow \operatorname{GL}_n
\]
be a `MatrixRepresentation` of
`VectorGroup.groupScheme (CommRingCat.of k) 1`. The vector space on which
the operators act is the full space of column vectors \(n\to k\).
There is no infinitude or characteristic assumption on \(k\).

`univariateMatrix` converts the actual universal polynomial matrix from
`VectorGroupPolynomial.polynomialMatrix` to a matrix \(M(X)\) with entries
in \(k[X]\), using `MvPolynomial.uniqueAlgEquiv` for the singleton variable
type `Fin 1`. The lemma `univariateMatrix_aeval` identifies \(M(t)\) with
the actual affine matrix of \(\rho\) at the vector-group point with
coordinate \(t\), for every commutative \(k\)-algebra of the specified
universe. This is an equality over the entire test algebra, with no
reducedness assumption. It follows from the multivariate evaluation
comparison and the evaluation compatibility of the polynomial equivalence.

`univariateMatrix_add` proves
\[
 M(s+t)=M(s)M(t)
\]
over every such test algebra. Its proof uses the actual vector-group
addition law and the monoid-homomorphism law of the representation.

`coefficientMatrix ρ m` is the matrix \(A_m=[X^m]M(X)\).
`dividedPower ρ m` is the already constructed coefficient operator
at the multi-index `Finsupp.single (0 : Fin 1) m`.
The lemma `dividedPower_eq_toLin` identifies it with
`Matrix.toLin' (coefficientMatrix ρ m)` by the coefficient compatibility
of `uniqueAlgEquiv`.

The main coefficient identity is
\[
 A_a A_b=\binom{a+b}{a}A_{a+b}.
\]
To prove `coefficientMatrix_mul`, the module evaluates the actual
representation law over the iterated polynomial algebra \(k[X][Y]\),
at \(s=Y\) and \(t=X\). Taking the coefficient of \(Y^a\), followed by
the coefficient of \(X^b\), gives the two sides. On the addition side,
Taylor expansion identifies the outer coefficient with the \(a\)-th
Hasse derivative of \(M\); `hasseDeriv_coeff` gives the displayed
binomial factor. On the product side, \(M(Y)\) has constant inner
coefficients and \(M(X)\) is constant in the outer variable, so these
two coefficient extractions give the matrix product \(A_a A_b\).
This polynomial-algebra calculation is valid over finite fields as well.

The actual identity point gives `coefficientMatrix_zero`, namely
\(A_0=1\). Transport through the matrix-to-linear-map equivalence proves
`dividedPower_zero` and `dividedPower_mul`:
\[
 D_0=1,\qquad D_aD_b=\binom{a+b}{a}D_{a+b}.
\]
Here multiplication of endomorphisms is composition. Binomial symmetry
then proves `dividedPower_commute`.

`dividedPower_eventually_zero` gives a natural number \(N\) such that
\(D_m=0\) for every \(m\ge N\). The bound is one more than the maximum
value at the unique variable of a multi-index in the finite support of
the actual coefficient family. Finally, induction using
\(D_1D_m=(m+1)D_{m+1}\) proves `dividedPower_one_pow`:
\[
 D_1^m=(m!:k)D_m.
\]

The provenance is an elementary derivation from actual polynomial
representation matrices and their representation law, using the
imported Mathlib polynomial equivalence, Taylor and Hasse-derivative
identities. No external existence or representation-theoretic theorem
is assumed. The module supplies a prerequisite for actual root-action
arguments. It constructs no root subgroup, highest-weight module or
Steinberg module, and does not prove `SteinbergBigCellStatement`.
