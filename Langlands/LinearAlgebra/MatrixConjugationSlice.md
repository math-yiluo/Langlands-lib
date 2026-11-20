# Local transverse slices for real matrix conjugation

For a real square matrix \(C\), write \(T\) for the image of \(X\mapsto XC-CX\). Let \(W\) be any linear complement to \(T\) in the matrix space. A linear right inverse \(J\) of the commutator onto \(T\) gives the product chart near \((0,0)\) in \(T\times W\) with formula

\[
(t,w)\longmapsto (1+J(t))(C+w)(1+J(t))^{-1}.
\]

Both chart directions are smooth. The chart uses the direct sum \(T\oplus W\) to parametrize the affine conjugation chart and restricts to a neighborhood on which \(1+J(t)\) is a unit.

There is a neighborhood of \((C,C)\) in the product of the ambient matrix space with itself with the following property. For a pair \((C+w,B)\) in that neighborhood, if the rank of \(X\mapsto X(C+w)-BX\) is at most \(\dim T\), then \(B\) lies in the chart and its inverse has second coordinate \(w\).

The proof chooses a smooth near-identity intertwiner \(g\) with \(g-1\) in the image of the same right inverse \(J\). The commutator applied to \(g-1\) recovers the first chart coordinate. The projection of the first matrix minus \(C\) onto \(W\) recovers the second. These two coordinates vary continuously and vanish at the base pair, so the neighborhood can be chosen to put them in the chart source. The intertwiner equation then identifies their chart image with \(B\). This is an internal local coordinate construction.
