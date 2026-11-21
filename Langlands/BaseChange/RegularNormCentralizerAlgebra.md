# The norm condition in a regular centralizer algebra

Let \(E\) be a commutative algebra over a field \(F\) with a cyclic generator
\(\sigma\) of degree \(\ell\), in the sense of `IsCyclicAlgebra σ l`. For a
regular semisimple element \(\gamma\) of \(\mathrm{GL}_n(F)\), let \(P\) be the
characteristic polynomial of the scalar-extended matrix \(A\). Write
\(B=E[X]/(P)\) and \(x\) for the class of \(X\). The automorphism \(\sigma_B\)
applies \(\sigma\) to the coefficients and fixes \(x\).

`RegularNormCentralizerAlgebraStatement` says that \(\gamma\) is a norm in
`IsNorm σ l` precisely when there is a unit \(b\) of \(B\) with
\[
\prod_{i=0}^{\ell-1}\sigma_B^i(b)=x.
\]

Evaluation at \(A\) descends to \(B\) by Cayley–Hamilton. A cyclic vector for
\(\gamma\) extends to a cyclic vector for \(A\). Applying a linear combination
of powers of \(A\) to this vector shows that evaluation is injective. The
cyclic-basis description of the matrix centralizer then gives preimages of a
commuting matrix and its inverse. Injectivity shows that these preimages are
inverse units.

For the forward implication, twist-conjugate the witness for `IsNorm` so that
its cyclic norm is exactly \(A\). The cyclic norm identity and \(\sigma(A)=A\)
show that this new witness commutes with \(A\). Equivariance of evaluation and
its injectivity identify the cyclic product of the corresponding unit with
\(x\). Conversely, evaluation of a unit satisfying the product condition gives
a matrix whose cyclic norm equals \(A\).

This is an internal algebraic reduction for the centralizer norm argument in
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), Chapter 1, Lemma 1.3, pp. 8–9. The formal statement uses
the cyclic product on the scalar-extended characteristic algebra.
