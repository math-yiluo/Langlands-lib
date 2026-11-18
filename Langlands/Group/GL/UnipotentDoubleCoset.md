# Monomial representatives of upper-unipotent double cosets

`monomialRepresentative w d` is the product of the published permutation matrix for `w` and the diagonal matrix with entries `d`. This internal coordinate model identifies the double cosets of the upper-unipotent subgroup in `GL_n(K)` for any field `K`.

For existence, the upper triangular Bruhat cells cover the group. On a given cell the Library's algebraic coordinates express the element as a product of an upper triangular matrix, the permutation representative, and an upper-unipotent matrix. Splitting the upper triangular factor by the existing torus equivalence gives the stated representative. Moving its torus factor through the permutation places it in the chosen column convention.

Uniqueness of the permutation is the Library's Bruhat cell index uniqueness. For the same permutation, any relation between two representatives can be rearranged to equate a permutation conjugate of a unipotent matrix with a unipotent matrix multiplied on the left and right by the two diagonal factors. At each diagonal entry the unipotent entries equal one. Equality then forces the two unit parameters in that column to coincide.
