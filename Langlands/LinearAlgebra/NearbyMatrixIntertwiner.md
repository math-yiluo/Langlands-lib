# Smooth near-identity intertwiners

For real square matrices \(A\) and \(B\), `matrixIntertwinerMap` sends \(X\) to \(XA-BX\). If a unit \(u\) satisfies \(uA=Bu\), then applying the map to \(uX\) gives \(u(XA-AX)\). Left multiplication by \(u\) is a real linear equivalence, so the range has the same dimension as the infinitesimal conjugation range at \(A\).

Fix a real square matrix \(C\), let \(T\) be the infinitesimal conjugation range at \(C\), and prescribe a linear right inverse \(J\) with domain \(T\). Choose a linear projection \(P\) onto \(T\). The projected map \(M(A,B)\) on \(T\) sends \(v\) to \(P(J(v)A-BJ(v))\). At \((C,C)\) it is the identity. On an open neighborhood where \(M(A,B)\) is invertible, the formula

\[
g(A,B)=1+J\bigl(M(A,B)^{-1}P(B-A)\bigr)
\]

is smooth and satisfies \(P(g(A,B)A-Bg(A,B))=0\). It equals \(1\) at \((C,C)\), so shrinking the neighborhood makes \(g\) a unit everywhere on it. The restriction of \(P\) to the range of the intertwiner map is surjective because \(M(A,B)\) is invertible. When that range has dimension at most \(\dim T\), the restriction is also injective, and the projected equation implies \(g(A,B)A=Bg(A,B)\). This is an internal finite-dimensional construction for local matrix conjugation coordinates.
