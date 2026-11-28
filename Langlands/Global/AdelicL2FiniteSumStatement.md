# Finite vectors of a finite orthogonal sum in adelic \(L^2\)

Let \(F\) be a number field and \(G\) an affine, locally finite-type
connected reductive group over \(F\), in the universe of the canonical
quotient. Use right translation on \(L^2([G])\) with the canonical
quotient measure. For a subgroup \(K\) of the adelic group, let \(K_\infty\)
be its inverse image in the archimedean factor.

`canonicalL2FiniteSubmodule` intersects the finite-orbit-span submodule
for \(K_\infty\) with the smooth submodule for the finite adelic group.
Here finite-adelic smoothness means invariance under one open subgroup.
`mem_canonicalL2FiniteSubmodule` identifies its membership with the
existing predicate `IsCanonicalL2FiniteVector`.

`AdelicL2FiniteSumStatement` takes a finite orthogonal family of closed
subspaces invariant under the canonical right action. Orthogonal
projection to the family identifies the finite vectors in its sum with
the product of the finite-vector subspaces of the summands. The inverse
adds the components in \(L^2([G])\). The finite index makes this product
the algebraic direct sum. Equivariance of orthogonal projection for the
unitary right action preserves compact orbit finiteness and open finite
levels. A finite sum of components has compact orbit contained in the
sum of their finite-dimensional orbit spans, and the intersection of
their open finite levels fixes it.

This is the finite-sum argument used inside the isotypic component in
Getz–Hahn, *An Introduction to Automorphic Representations*
(`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`),
Theorem 9.7.3 and its proof of (9.40), printed pp. 265–266 (PDF pp. 277–278).
The two finiteness conditions follow §6.6, (6.24) and the paragraph
following it, printed pp. 170–171 (PDF pp. 184–185). Those passages use
a maximal compact at infinity and, in (9.40), mutually equivalent
irreducible summands. The projection and summation argument applies to
any supplied invariant orthogonal finite family. The proposition
specifies the underlying linear isomorphism between spaces of Hilbert
vectors. Infinitesimal actions and the comparison of irreducible
isomorphism classes require further results.
