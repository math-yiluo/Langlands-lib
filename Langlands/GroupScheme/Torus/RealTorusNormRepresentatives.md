# Representatives for real torus points modulo norms

Let \(K\) be a field isomorphic to \(\mathbb R\), let \(M\) be its algebraic closure, and let \(T\) be a torus over \(K\). For every \(K\)-point \(p\) there is a Galois-invariant cocharacter \(\nu\) of \(T_M\) and an \(M\)-point \(r\) such that

\[
p_M = \nu(-1)\bigl(r\,\sigma(r)\bigr).
\]

Here \(\sigma\) is the nonidentity element of \(\operatorname{Gal}(M/K)\). The Lean equality is on the coefficient points over \(M\), where the product of the two conjugates represents the quadratic norm.

The proof takes a square root \(r\) of \(p_M\) in split torus coordinates. Since \(p_M\) is fixed by \(\sigma\), the point \(r/\sigma(r)\) has square one. Its character values define a sign functional on the character lattice. An anti-invariant character takes that point to the norm of its value at \(r\), which cannot be \(-1\) because complex norms are nonnegative. The involutive lattice sign lemma lifts the sign functional to an invariant integral functional. The perfect lattice pairing gives \(\nu\), and evaluation of characters proves \(r/\sigma(r)=\nu(-1)\).
