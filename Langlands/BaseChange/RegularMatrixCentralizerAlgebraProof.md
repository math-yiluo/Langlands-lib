# The étale centralizer algebra of a regular matrix

`Langlands.BaseChange.regularMatrixCentralizerAlgebra` proves
`RegularMatrixCentralizerAlgebraStatement`. For a matrix \(A\) of size \(n\)
over a field \(F\), write \(p=\operatorname{charpoly}A\). Separability gives
a Bézout identity \(ap+bp'=1\), which supplies the relation in
`StandardEtalePair` for \(p\) and the polynomial \(1\). The associated
standard étale algebra is the localization of \(F[X]/(p)\) at the class
of \(1\). The proof uses the algebra equivalence for localization at a
unit to transport étaleness to \(F[X]/(p)\). The quotient dimension is
the degree of \(p\), which equals \(n\).

`regularCyclicBasis` supplies a cyclic vector, and
`charpolyRootEvaluation_injective` uses the cyclic basis to prove injectivity
of evaluation at \(A\). Every element of the commutative quotient commutes
with the class of \(X\), so its image commutes with \(A\).
Conversely, `exists_sum_pow_of_commute` writes any matrix \(B\) commuting
with \(A\) as \(\sum_{j<n} c_j A^j\). The class of
\(\sum_{j<n} c_j X^j\) evaluates to \(B\).

The same proof applies at \(n=0\), where \(p=1\), the quotient is the zero
algebra of dimension zero, and the polynomial sum is empty.

This calculation supplies the characteristic-polynomial algebra comparison
for the general linear group in the maximal-torus setting of David Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026, § V.2.1,
printed p. 104 (PDF p. 110).
