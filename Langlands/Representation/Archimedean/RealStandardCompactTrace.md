# Invariance of compact polynomial traces on real standard modules

`averageTrace` is the trace of the operator \(f \mapsto
\int_{O(n)} \varphi(k) f(\,\cdot\,kg)\,dk\) on its finite-dimensional
range. Here \(\varphi\) is a polynomial in the entries of \(k\) and
\(g\) is any real invertible matrix. `realStandardCompactTrace` proves
equality of these traces on two actual real standard modules with a
bijective compact and Lie intertwiner.

The Library represents the pullback of each compact pairing against a
dual principal series vector by a pairing on the source. Its matrix
coefficient transfer identity then gives equality of the pairings
after right translation by any group element. Fubini gives the same
equality after averaging over \(k\). Separation by dual principal series
vectors shows that averaging commutes with the intertwiner, even for
intertwiners that are only linear maps. A bijective intertwiner
restricts to an equivalence between the two finite-dimensional ranges,
so their endomorphisms have equal trace by conjugation invariance.

This internal result applies the pairing transpose and matrix coefficient
transfer of `RealReverseTransfer` to the operators of
`RealStandardCompactAverage`. The resulting traces are the finite-rank
quantities used in comparing regular Cartan characters.
