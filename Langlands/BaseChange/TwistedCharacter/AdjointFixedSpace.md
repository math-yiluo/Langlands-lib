# Fixed spaces of the twisted matrix adjoint action

`twistedMatrixConj_mul` and `twistedMatrixConj_pow` express the semidirect
product law and identify the adjoint power by the cyclic norm. The
linear equivalence `twistedAdjointFixedConjEquiv` identifies the fixed
spaces at two twisted-conjugate elements by conjugating matrices.

Let \(F\) be a field and \(E\) a cyclic \(F\)-algebra of degree \(l\)
with generator \(\sigma\), in the sense of `IsCyclicAlgebra σ l`. Assume
the norm of \(\delta\) equals the scalar extension of a base matrix
\(\gamma\) satisfying `IsRegularSemisimple γ`. The cyclic-vector basis
makes the scalar-extended matrix centralizer commutative, and the twisting
matrix belongs to that centralizer. Since \(\sigma^l=1\), the adjoint
power formula shows that a fixed matrix commutes with the norm. Its
fixed-point condition then reduces to entrywise \(\sigma\)-invariance.
The cyclic algebra's fixed-scalar condition makes those entries descend
to \(F\). Evaluation of \(F[X]/(\operatorname{charpoly}(\gamma))\) and
scalar extension identify that algebra with the fixed space because
every matrix commuting with the cyclic base matrix is a polynomial in it.

For the same cyclic algebra, `IsSigmaRegular σ l δ` supplies a regular
semisimple norm associate. Twisted conjugation reduces its norm
association to equality, and the characteristic polynomial degree gives
`finrank_twistedAdjointFixed_of_sigmaRegular`. This computes the
geometric multiplicity of \(1\) as \(n\) over \(F\).

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula*, Chapter 1, Proposition 2.2, printed pp. 11–12, uses
the adjoint fixed space on the generator component. Source ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
