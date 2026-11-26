# Cyclic extension of a twisted representation

For positive \(l\), `cyclicPowerHom` sends the generator of
\(\mathbb Z/l\mathbb Z\) to a monoid element whose \(l\)-th power is one.
Let \(G\) be a group with a topology and \(\rho\) an irreducible admissible
complex representation of \(G\). Let \(\theta\) be an automorphism with
\(\theta^l=1\) and \(A\) an intertwining isomorphism from \(\rho\) to
\(\rho\circ\theta\). The proof of `exists_normalizedCyclicIntertwiner`
places \(A^l\) in the commutant and applies admissible Schur's lemma.
Invertibility makes the resulting scalar nonzero. Taking an \(l\)-th
root \(c\) in \(\mathbb C^\times\) gives an intertwining isomorphism
\(B=c^{-1}A\) satisfying \(B^l=1\). The identity \(A=cB\) retains the
scalar needed to recover the character of the given \(A\).

For a complex representation \(\rho\), `cyclicExtension` takes a linear
endomorphism \(B\) with \(B^l=1\) and
\(B\rho(g)=\rho(\theta(g))B\). It acts on the same vector space by
\((g,i)\mapsto \rho(g)B^i\). The normalization makes powers depend only
on the cyclic exponent, and the intertwining identity gives the
representation law. When \(\rho\) is irreducible,
`cyclicExtension_irreducible` restricts an invariant subspace to the copy
of the original group at exponent zero to show that the extension is
irreducible.
`entrywiseAutHom` packages the entrywise automorphisms of \(\mathrm{GL}_n\) of
a commutative algebra as a homomorphism.

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula*, Chapter 1, §2.1, printed pp. 10–11, explains the normalization
and extension for a cyclic field extension. Source ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The algebraic normalization and extension arguments use the hypotheses above
for any group with the stated automorphism.
