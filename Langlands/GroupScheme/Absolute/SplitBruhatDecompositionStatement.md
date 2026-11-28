# The split Bruhat decomposition of the group and flag quotient

`Langlands.GroupScheme.SplitBruhatDecompositionStatement` concerns a Borel pair
\((B,T)\) in a connected reductive group \(G\) over a field \(k\), with \(T\)
split. It chooses a regular cocharacter \(\chi\) of \(T\) for which the given
inclusion of \(B\) represents \(P_G(\chi)\). Write \(U=U_G(\chi)\) and
\(V=U_G(\chi^{-1})\) for the represented unipotent groups.

For each element \(w\) of \(N_G(T)(k)/C_G(T)(k)\), the statement chooses a
representative \(n_w\) over \(k\) and uses the scheme-theoretic intersection
\(W_w=U\cap n_w Vn_w^{-1}\). The group cell is the multiplication map
\(W_w\times B\to G\), \((a,b)\mapsto a n_w b\). Given a smooth, surjective,
quasi-compact \(q:G\to Q\) whose fibres on scheme tests are exactly the right
\(B\)-cosets, the flag cell is \(W_w\to Q\), \(a\mapsto q(a n_w)\).
Each family consists of locally closed immersions. Every underlying scheme
point and every point on a field-valued test belongs to exactly one of the
corresponding images.

This is the disjoint decomposition in Milne, *Algebraic Groups* (2017),
Theorem 21.73(a) and Remark 21.74, printed p. 447 (PDF p. 463). The intersection
and flag parametrization are those of Definition 21.76 and Proposition
21.79(b), printed pp. 448–449 (PDF pp. 464–465). The author erratum to
Proposition 21.71 calls for a covering argument for the orbit equality on
which Theorem 21.73 relies. The statement here specifies the decomposition
using the actual multiplication and flag maps and the Weyl group over \(k\).
