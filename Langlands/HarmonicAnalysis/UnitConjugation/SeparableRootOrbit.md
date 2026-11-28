# Clopen conjugacy orbits in the root locus of a separable polynomial

`SeparableRootOrbitClopenStatement` concerns an associative algebra \(A\) over a
commutative ring \(F\). It requires continuous ring operations and constant
scalar multiplications on \(A\), and an open unit locus. If \(s\) is a root of
\(p\in F[T]\) and \(p\) is coprime to its formal derivative, the conjugacy orbit
of \(s\) under \(A^\times\) is clopen in the subspace of all roots of \(p\) in
\(A\). The two universes are independent.

For a monomial of degree \(n\), the divided difference is the sum of the products
\(x^i y^{n-1-i}\) over \(0\leq i<n\). Its recursion uses left multiplication by
\(x\) and addition of \(y^n\). The resulting polynomial divided difference
\(d(x,y)\) satisfies \(xd(x,y)-d(x,y)y=p(x)-p(y)\) and \(d(y,y)=p'(y)\).
Evaluating a Bézout identity shows that \(p'(y)\) is a unit whenever \(p(y)=0\).
For fixed \(y\) the divided difference is continuous in \(x\), so it stays a unit
in a neighborhood of \(y\). It then conjugates \(y\) to every nearby root \(x\).
Membership in the orbit of \(s\) is locally constant on the root locus, proving
openness of the orbit and of its relative complement.

The result gives local separation of semisimple conjugacy classes through a
fixed separable annihilating polynomial. This is an associative-algebra
argument for use in the neighborhood constructions in Harish-Chandra,
*Admissible invariant distributions on reductive p-adic groups* (AMS, 1999),
§2, Corollary 2.4 and Lemma 2.8, printed pp. 15–16.
