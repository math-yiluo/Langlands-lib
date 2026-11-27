# Conjugacy of regular matrix centralizer algebras

`Langlands.BaseChange.RegularCentralizerAlgebraConjugacyStatement` concerns
two matrices \(A,B\) of the same size over a field \(F\), each with a
separable characteristic polynomial. For any \(F\)-algebra isomorphism
between \(F[X]/(\operatorname{charpoly}A)\) and
\(F[X]/(\operatorname{charpoly}B)\), a single matrix \(g\in\mathrm{GL}_n(F)\)
implements that isomorphism by conjugation on their images under
`charpolyRootEvaluation`. The given isomorphism determines the image of
the distinguished root of the first quotient. This image can differ
from the distinguished root of the second quotient.

The comparison comes from the cyclic-vector representation of each
characteristic-polynomial algebra on \(F^n\). The evaluation maps and
`Langlands.BaseChange.regularCyclicBasis` supply the data for the two
regular representations. This is an algebraic step toward the
\(\mathrm{GL}_n\) case of Renard's rational maximal-torus finiteness in
§ V.2.1, printed p. 104 (PDF p. 110) of the 9 July 2026 edition.
