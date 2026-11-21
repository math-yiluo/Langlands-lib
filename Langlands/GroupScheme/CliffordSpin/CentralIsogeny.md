# The scalar Clifford central isogeny

`ScalarCliffordCentralIsogenyStatement` concerns a scalar quadratic presentation of positive dimension over a characteristic-zero field. If its polar matrix is nonsingular, the vector action `projection` is a central isogeny onto the actual norm-one isometry group of the presentation.

`isCentralIsogeny_projection` proves the claim. The Clifford lift group is the spectrum of a quotient of the tensor product of the coordinate rings of the Clifford unit group and the general linear group. Those rings have finite type over the ground field. The target is an affine closed subgroup of the matrix-algebra unit group. It has finite type and is smooth by Cartier's theorem. Geometric surjectivity therefore gives flatness.

The actual kernel is μ₂. Its inclusion into the one-dimensional diagonalizable group is closed and all its scheme-valued points have exponent dividing two, which gives finiteness over the ground field. Finiteness descends to the projection by the finite-kernel criterion for fpqc group homomorphisms. The target is locally Noetherian, so the finite projection is locally of finite presentation. Centrality follows from the scalar kernel formula on all tests.

The central isogeny is the group-scheme version of the scalar spin covering used in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99. The proof uses the full affine Clifford equations and the Library's finite-kernel descent theorem.
