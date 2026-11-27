# Unitary involutions in the universe of the base field

`BaseUniversePair.ofFinite` presents a finite field extension \(K/F\)
and a finite-dimensional central simple \(K\)-algebra in the universe
of \(F\). The extension and the given algebra can start in a separate
universe. The presentation includes an \(F\)-algebra equivalence on the
center, a ring equivalence on the algebra, and the compatibility of the
two equivalences with scalar multiplication.

Both carriers are finite modules over \(F\), so they admit `Shrink`
presentations in its universe. Transport along the equivalences
preserves simplicity, centrality, and the two dimensions.
`BaseUniversePair.centerAutomorphism` and `BaseUniversePair.involution`
conjugate the center automorphism and the algebra involution by the
respective equivalences. The scalar relation transports the unitary
involution law and a nonidentity center action stays nonidentity.
