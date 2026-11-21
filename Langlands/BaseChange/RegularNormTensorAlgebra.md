# The regular norm condition over the base characteristic algebra

Let \(F\) be a field and let \(E/F\) be a finite commutative cyclic algebra
with generator \(\sigma\) of degree \(\ell\) in the sense of `IsCyclicAlgebra`.
For a regular semisimple \(\gamma\in\mathrm{GL}_n(F)\), set
\(B=F[X]/(\operatorname{charpoly}(\gamma))\) and write \(x\) for the class of
\(X\). Then `RegularNormTensorAlgebraStatement` says that \(\gamma\) is a norm
in `IsNorm σ l` if and only if some unit \(b\) of \(B\otimes_F E\) satisfies
\[
\prod_{i=0}^{\ell-1}(1\otimes\sigma)^i(b)=x\otimes 1.
\]

The proof constructs the scalar extension of an adjoined root by the two
universal properties. It checks the inverse maps on the original generator
and the coefficient maps. The characteristic polynomial commutes with
scalar extension, so this equivalence identifies the distinguished roots.
On the two factors of the tensor product, the coefficient automorphism
corresponds to the identity on \(B\) and \(\sigma\) on \(E\). Transporting
units and cyclic products through the equivalence gives the statement from
`RegularNormCentralizerAlgebraStatement`.

This internal reduction implements the tensor product in the centralizer
norm argument of Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula* (1989), Chapter 1, Lemma 1.3, pp. 8–9.
