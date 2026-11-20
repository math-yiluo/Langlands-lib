# Cartan covering and contraction for finite products

The coefficient-ring isomorphism sends each matrix to the family of its
component matrices and sends inverse matrices to the corresponding inverses.
The two maps are continuous in the entry topologies. The same isomorphism
restricts to upper triangular matrix units because vanishing below the
diagonal is checked in each component.

Use the product of the supplied compact open subgroups and the product of
the supplied sets of representatives. Each double-coset factorization is
chosen in its own coordinate. For an ambient open subgroup, pull it back
along the inclusion of each single coordinate and apply the contraction in
that factor. The resulting compact open subgroups in the triangular groups
give a compact open product. After conjugation, each single-coordinate term
belongs to the ambient open subgroup. Their finite product is the full
conjugate, so it belongs to that subgroup as well.

This is an internal transport of the Cartan input used in the
Harish-Chandra averaging argument.

`FiniteAlgebraUpperTriangularCartanStatement` applies the property to a
reduced finite algebra over a nonarchimedean local field, with the module
topology on the algebra. In `finiteAlgebraUpperTriangularCartan`, the
algebra is Artinian and its factors are the quotients by its maximal
ideals. Each quotient is a finite field extension and carries its
spectral local-field topology. This is the quotient field's module
topology over the base field by finite-dimensionality. The finite
product of these topologies is the module topology, so the Artinian
algebra isomorphism and its inverse are continuous. The product theorem
then applies to the field Cartan covering and contraction in every
factor.
