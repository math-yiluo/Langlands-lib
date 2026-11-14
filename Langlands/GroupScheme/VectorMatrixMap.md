# Matrix homomorphisms of polynomial vector groups

For a matrix over any commutative ring, `matrixHom` is an actual homomorphism
between polynomial vector group schemes. On every scheme test its coordinates
are obtained by multiplying the column of global-section coordinates by the
matrix, after mapping its coefficients through the test's structure morphism.
The finite-sum formula is additive and natural under all scheme morphisms.

Composition is matrix multiplication in column-coordinate order. The identity
matrix gives the identity, diagonal matrices recover the existing diagonal
maps, and invertible square matrices give actual group-scheme isomorphisms.
The construction commutes with change of the coefficient ring, via the
canonical base-change isomorphisms of polynomial vector groups.

These are internal constructions from the existing all-test vector coordinates
and Yoneda realization of natural homomorphisms. They support the additive
integral models of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Section C.2, printed pp.697–698 (PDF pp.728–729), when lattice bases at different
depths have general matrix transitions. They do not themselves construct
root-group models or identify a supplied apartment filtration.
