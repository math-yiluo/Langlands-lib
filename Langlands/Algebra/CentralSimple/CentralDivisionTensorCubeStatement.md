# A degree-six central division algebra cannot have a split tensor cube

`Langlands.CentralSimple.CentralDivisionDegreeSixTensorCubeNonSplitStatement`
is an unproved arithmetic proposition over every field and in every
characteristic. It quantifies over an actual finite-dimensional central
division algebra \(D/k\) with \(\dim_kD=36\), and asserts that the actual
algebra \((D\otimes_kD)\otimes_kD\) is not isomorphic to a positive-size
matrix algebra over \(k\). Both the field and the algebra lie in `Type u`,
for every universe parameter `u`.

The dimension condition expresses reduced degree six without requiring a
separate degree API. No group law on a quotient of central simple
algebras is assumed. In particular, the conclusion is a statement about
actual tensor products and actual algebra isomorphisms.

This is a derived specialization of the usual index–exponent prime
support theorem. The source is Knus–Merkurjev–Rost–Tignol,
*The Book of Involutions* (1998), §1, printed pages 3–4, and the proof of
Corollary (2.8), printed page 18. Page 4 defines reduced degree, index,
splitting and the tensor-product Brauer group. Page 18 states that
index and exponent have the same prime factors, citing Draxl [84],
Theorem 11, page 66.

For this specialization, a division algebra of degree six has index six.
A split tensor cube would make the exponent divide three. Equal prime
support would then contradict the factor two of the index. This
paragraph explains the intended mathematical derivation; the Lean file
does not yet implement that proof.

The registered source identifier is
`knus-merkurjev-rost-tignol-1998-book-of-involutions`, with content SHA256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.
The retained author errata and the relevant entries of the separate
page-sorted comments were checked. Their page-17 correction concerns
Proposition (2.7); no retained entry changes the page-18 prime-support
sentence or the cited page-4 definitions.

The intended group-scheme application still requires an independent
construction of the actual Tits obstruction and its comparison with the
actual anisotropic kernel. This arithmetic proposition asserts neither
of those inputs.
