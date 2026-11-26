# One-parameter factorization of genuine smooth vectors

Let \(A\) be a finite-dimensional real Banach algebra, and let \(R\) be a
jointly continuous representation of \(A^\times\) on a complex Banach space.
For each genuine smooth vector \(v\), direction \(X\in A\) and \(\epsilon>0\),
there are a smooth vector \(w\) and two smooth scalar kernels \(g,k\) on
\(\mathbb R\), each supported in \([0,\epsilon]\), such that every continuous
linear scalar functional \(L\) on the smooth space satisfies
\[
L(v)=\int g(t)L(R(\exp(tX))w)\,dt
    +\int k(t)L(R(\exp(tX))v)\,dt.
\]
The group actions in this formula are the actions on the genuine smooth space.

The units-chart derivative identifies the \(p\)-th derivative of a scalar
exponential orbit with the orbit of \(dR(X)^p v\). On the compact time
interval, choose a nonnegative bound for every derivative order and every
word-order seminorm. The bound for index \(p\) used in the scalar
Dixmier–Malliavin identity is one plus the sum of the bounds for the
seminorm orders through \(p\). The resulting coefficients give an
absolutely summable series in every fixed genuine word coordinate.
The closed image of the derivative coordinates makes that series a
smooth vector \(w\).

Integrate the two smooth orbits using the genuine word integral. The
scalar Dirac identity, applied to norm-bounded functionals of the empty
word, shows that the sum of those two vectors has the same empty word as
\(v\). The summable bounds justify interchanging the integrals and the
series. Hahn–Banach separates vectors in the Banach carrier, and the
empty word is injective on smooth vectors. Continuous evaluation then
gives the displayed formula for all \(L\).

This is the one-parameter case of the vector factorization used in
H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Lemma 6.1,
author-posted p. 37, and in the proof of Lemma 14.1, p. 106.
The underlying construction is in J. Dixmier and P. Malliavin,
*Factorisations de fonctions et de vecteurs indéfiniment différentiables*
(1978), Lemma 2.5, Remark 2.6, and the proof of Theorem 3.3, pp. 5–6 and
8–9 in the retained English translation. The Lean construction uses the
one-dimensional Dirac identity with support in \([0,\epsilon]\) and
works in the genuine word-coordinate realization of the smooth space.
