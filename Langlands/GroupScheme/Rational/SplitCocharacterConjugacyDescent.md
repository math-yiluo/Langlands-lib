# Conjugacy and field descent of cocharacters for split reductive groups

`SplitCocharacterConjugacyDescentStatement` states that if \(G\) is a
connected reductive group with a split maximal torus over \(K\), then
every cocharacter of \(G_L\) for an algebraic field extension \(L/K\)
is conjugate by a point of \(G(L)\) to the pullback of a cocharacter
of \(G\). The conjugacy is an equality of group-scheme homomorphisms.

`splitCocharacterConjugacyDescent` fixes a split maximal \(K\)-torus \(T\)
of \(G\). Its pullback to \(L\) remains split and maximal. The given
cocharacter factors through a maximal \(L\)-split torus, which
`maximalSplitTorusConjugacy` conjugates to \(T_L\) by a point over \(L\).
The resulting cocharacter of \(T_L\) pulls back from a cocharacter of
\(T\) by `IsSplitTorus.existsUnique_baseChangeCocharacter`. The proof
uses the inverse of the conjugating point to recover the given
cocharacter from this pullback.
