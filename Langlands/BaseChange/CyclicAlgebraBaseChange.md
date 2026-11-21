# Scalar extension of a cyclic algebra

Let \(E/F\) be a finite commutative cyclic algebra in the sense of
`IsCyclicAlgebra`, with generator \(\sigma\) of order \(\ell\). For any field
extension \(B/F\), the automorphism \(1\otimes\sigma\) of \(B\otimes_F E\)
fixes exactly the image of \(B\). If \(E/F\) is formally unramified,
`IsCyclicAlgebra.scalarExtension` gives the full cyclic algebra condition of
degree \(\ell\) over \(B\).

Scalar extension of an \(F\)-basis gives the dimension over \(B\). The map
on automorphisms is injective because \(e\mapsto 1\otimes e\) is injective,
so it preserves the order of \(\sigma\). The \(F\)-linear sequence
\[
F\longrightarrow E\xrightarrow{\sigma-1}E
\]
is exact at the middle term by the fixed-point condition. Tensoring it with
\(B\) preserves exactness by flatness. Its first map is the scalar map after
the canonical identification \(B\otimes_F F\simeq B\). Formal
unramifiedness is preserved by scalar extension and gives reducedness of
the tensor algebra over \(B\).

`CyclicAlgebraBaseChangeStatement` specializes this to characteristic zero.
Here the residue-field decomposition of \(E\) makes it a product of finite
separable fields over \(F\), hence formally étale. This internal result is
used when extending the cyclic algebra to a regular characteristic field
in the norm argument of Arthur–Clozel, *Simple Algebras, Base Change, and
the Advanced Theory of the Trace Formula* (1989), Chapter 1, Lemma 1.3,
pp. 8–9.
