# The twisted conjugation product in additive matrix coordinates

This internal lemma connects the Library's algebraic triangular differential
with the strict derivative needed for compact averaging. It uses the
finite-algebra operator norm on the full matrix algebra, with the given
matrix topology. Upper triangular matrices carry the induced norm.

The coordinate map sends \((y,k,p)\) to \(k y\,\sigma(k)^{-1}\sigma(p)\).
The inversion is the ring inverse on matrices. The joint strict derivative
on the open locus of invertible \(k\) follows from the continuous linear
projections, the strict derivative of inversion, and the noncommutative
product rule. These also give continuity there.

For the submersion statement, \(F\) is a complete nontrivially normed field
of characteristic zero, \(E\) is a finite reduced commutative \(F\)-algebra
with its module topology, and \(\sigma\) is an \(F\)-algebra automorphism of
\(E\). Assume \(\sigma^l=1\), let \(\delta\) be \(\sigma\)-regular for the
length-\(l\) norm, and take \(k\) invertible and \(p\) invertible upper triangular.
Put \(d=k\delta\sigma(k)^{-1}\) and \(w=d\sigma(p)\). On a source direction
\((Xk,Yp)\), with \(Y\) upper triangular, the derivative is
\[
\bigl(X-d\sigma(X)d^{-1}+d\sigma(Y)d^{-1}\bigr)w.
\]
The law \(\sigma^l=1\) transfers the regular norm witness from \(\delta\) to
its twisted conjugate \(d\).
The algebraic surjectivity theorem supplies \(X,Y\) for any value of the
parenthesized expression, and right multiplication by \(w\) is invertible.
This proves surjectivity of the partial strict derivative. The coordinate
formula agrees with the group product at all unit triples.

The algebraic formula comes from the trace-pairing step of
Henniart–Lemaire, I.2.7, Lemma 1, as implemented in
`Langlands.BaseChange.TwistedTriangularDifferential`. The joint derivative
keeps the parameter explicit for the compact pushforward argument of
Harish-Chandra, 1981, Sections 2–4.
