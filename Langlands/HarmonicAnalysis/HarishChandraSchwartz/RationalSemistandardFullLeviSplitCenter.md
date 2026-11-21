# The split center at the full standard semistandard index

Waldspurger uses \(A_G\) for the split component of \(G\) in I.1. The
last paragraph of VIII.5 compares the Fourier component with parabolic
\(G\) to the action of each discrete series of \(G\). In Lean the Levi
at that index is a literal subgroup, and its split component is
specified on a representing group scheme. `FullLeviSplitCenterStatement`
identifies its rational-point image with the point image of the
ambient split component under the full-Levi equivalence.

`fullLeviSplitCenter_map` factors the ambient split component through
the full standard Levi isomorphism. Split-center choice independence
identifies the given model's point image with that of the factor on
the standard model. Both full-Levi identifications take a literal
Levi point to its underlying ambient point, so the previously proved
map formula for the factor gives the desired equality. The statement
uses no quotient Haar normalization.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
I.1 and VIII.5, printed p. 332 (PDF p. 98).
