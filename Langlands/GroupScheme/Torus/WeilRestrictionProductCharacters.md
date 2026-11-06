# Characters of Weil restrictions from products of intermediate fields

This internal construction identifies the actual character lattice of the Weil
restriction of the multiplicative group from a finite product of intermediate
fields of a prescribed finite Galois extension \(L/k\). The coordinate set is
the dependent disjoint union of the \(k\)-embeddings of the factors into \(L\).
Both fields and the finite factor index have arbitrary universe \(u\). Empty
products are allowed.

The module reuses `productEmbeddingDecomposition` from the shared
`WeilRestrictionProductDecomposition` pair. This algebra decomposition first
commutes scalar extension with the finite
product, then applies the published separable embedding decomposition to each
factor, and finally uncurries. Its coordinate formula is
\(c\otimes a\mapsto (c\tau(a_i))_{(i,\tau)}\).
The published algebra-decomposition construction supplies the actual splitting
isomorphism of commutative group schemes and the additive character equivalence.

On every test scheme the coordinates evaluate the original tensor unit through
the selected factor and embedding. Changing the coefficient structure by a
Galois automorphism \(\sigma\) postcomposes that embedding by \(\sigma\).
The character formula is a monomial in these coordinates. Reindexing its finite
product therefore shows that actual character transport sends a coefficient
function \(m\) to \((i,\tau)\mapsto m(i,\sigma^{-1}\circ\tau)\).

This is a direct derivation from the published tensor decomposition, its
test-scheme formulas, and canonical Galois descent. It assumes no classification
of tori and does not itself claim the induced-torus decomposition theorem.
