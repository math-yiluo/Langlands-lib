# The étale centralizer algebra of a regular matrix

`Langlands.BaseChange.RegularMatrixCentralizerAlgebraStatement` takes a
matrix \(A\) of size \(n\) over a field \(F\) with separable characteristic
polynomial. It asserts that the characteristic-polynomial algebra
\(F[X]/(\operatorname{charpoly}A)\) is étale of dimension \(n\). The
evaluation map `charpolyRootEvaluation A` is injective, and its image
consists of exactly the matrices commuting with \(A\). The statement
also permits size zero.

The étaleness comes from the derivative being a unit in the quotient.
The matrix comparison uses evaluation at \(A\) and the cyclic-vector
description of its commutant. This gives the bounded-dimensional
étale algebra used to compare maximal tori of \(\mathrm{GL}_n\) for
Renard, § V.2.1, printed p. 104 (PDF p. 110) of the 9 July 2026 edition.
