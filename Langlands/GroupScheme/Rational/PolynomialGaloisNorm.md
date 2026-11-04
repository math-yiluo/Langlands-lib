# Finite-Galois descent of actual polynomial points

This internal construction applies the coefficient-descent algebra map in
`PolynomialGaloisDescent` to the actual affine coordinate ring of an affine
group scheme. Coefficient extension identifies its multivariate polynomial
points over the base field with the subgroup fixed by the Galois action on
extension-field coefficients. The equivalence preserves the actual group
law because extension does and extension is injective.

Coefficient automorphisms preserve the center of the extension polynomial-point
group. Their full product is taken inside that commutative center. Left
multiplication permutes the automorphism group, so the product is fixed.
The equivalence descends the product to the base polynomial-point group.
Injectivity of extension shows that its descent is central there as well.
`PolynomialPoint.norm` is the resulting homomorphism between the two centers,
and `extend_norm` identifies its extension with the full conjugate product.

The polynomial variables remain fixed. The field extension is finite Galois;
the group scheme is arbitrary affine, and it need not be commutative. The
construction uses no division by the field degree. Centrality is centrality
in the indicated actual polynomial-point group; it is not asserted here to
be an all-test centrality condition. A homomorphism between group schemes,
nontriviality of a norm image, and split-unipotence descent remain to be
constructed or proved.
