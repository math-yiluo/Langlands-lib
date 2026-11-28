# Conjugacy of regular matrix centralizer algebras

`Langlands.BaseChange.regularCentralizerAlgebraConjugacy` proves that one
matrix in \(\mathrm{GL}_n(F)\) implements a given \(F\)-algebra isomorphism
\(e\) on the evaluated images of the two characteristic-polynomial algebras.
[Statement](RegularCentralizerAlgebraConjugacyStatement.md)

For each \(C\in\{A,B\}\), let \(R_C=F[X]/(\operatorname{charpoly} C)\)
and write \(\rho_C\) for `charpolyRootEvaluation C`. Separability gives a
cyclic vector \(v_C\) by `regularCyclicBasis`. The linear map
\(\iota_C(a)=\rho_C(a)v_C\) is injective. Indeed, \(\rho_C(a)\) commutes
with \(C\), and `eq_of_commute_mulVec_eq` shows that it is zero if it
kills \(v_C\). Then `charpolyRootEvaluation_injective` gives \(a=0\).
Both \(R_C\) and \(F^n\) have dimension \(n\), so \(\iota_C\) is a linear
isomorphism.

The proof forms \(\phi=\iota_B\circ e\circ\iota_A^{-1}\). For
\(a,b\in R_A\), multiplicativity of evaluation and of \(e\) gives
\[
  \phi\bigl(\rho_A(a)\iota_A(b)\bigr)
  =\iota_B(e(ab))
  =\rho_B(e(a))\phi(\iota_A(b)).
\]
Since every vector is \(\iota_A(b)\) for some \(b\), the matrix \(g\) of
\(\phi\) satisfies \(g\rho_A(a)=\rho_B(e(a))g\) for every \(a\in R_A\).
The proof concludes by multiplying on the right by \(g^{-1}\).
