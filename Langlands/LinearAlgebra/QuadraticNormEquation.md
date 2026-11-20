# Coordinate norm equations in quadratic algebras

These algebraic lemmas use Mathlib's `QuadraticAlgebra K a 0` for the algebra
with basis \(1,\omega\) and relation \(\omega^2=a\). Its determinant norm is
\(x^2-ay^2\) on \(x+y\omega\). If \(a\) is nonsquare, the canonical lift of
\(\omega\) to a root in a degree-two field extension is an algebra
isomorphism, by injectivity and equality of dimensions.

Over any field, a nonzero pair \((x,y)\) satisfying \(x^2-ay^2=0\) has
\(y\ne 0\), so that \(a=(x/y)^2\).

The split representation and ternary reduction in Lean use a field of
characteristic zero. For a nonzero square \(a=s^2\), the equations
\(x+sy=b\) and \(x-sy=1\) give a representation of any \(b\) by \(x^2-ay^2\).
For \(a\ne 0\) and a nonzero triple \((x,y,z)\) satisfying
\(x^2-ay^2=bz^2\), dividing by \(z^2\) gives the representation if
\(z\ne 0\). If \(z=0\), the binary zero implies that \(a\) is square,
so the split representation applies.

These are derived support lemmas for the norm interpretation of binary and
ternary forms in J. S. Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VIII, Lemma 3.4 and Proposition 3.7(b,c), printed pp. 235–236
(PDF pp. 244–245).
Registered source `milne-2020-class-field-theory`, SHA-256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
