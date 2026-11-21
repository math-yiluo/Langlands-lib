# Linear differential in ordinary Weyl coordinates

For a regular semisimple `γ` in `GL_n(F)` over any field `F`, let
`d = Ad(γ) − 1` and let `P` project onto its kernel along its image.
`OrdinaryWeylDifferentialStatement` says that `det(P − d)` is a unit
and equals the Library discriminant `weylDiscriminant γ`.

The kernel of `d` is the matrix centralizer. Evaluation at a cyclic vector
identifies it with the column space of dimension `n`. Commutators and powers
of `γ` span the matrix algebra by `exists_commutator_add_powers`, and
`X γ − γ X = d (−X γ)`. The kernel and image therefore span the space.
Rank-nullity and the dimension formula for a sum show that they are
complementary.

In this splitting, `P − d` is the identity on the kernel and the negative
of the restriction of `d` to its image. The latter block is injective
because the kernel and image intersect trivially, hence invertible in
finite dimension. The characteristic polynomial of `d` is `X^n` times
the characteristic polynomial of the range block of `d`. Its degree-`n`
coefficient is the constant term of the latter polynomial, which is
the determinant of the negative range block.

This internal linear algebra calculation uses the discriminant defined in
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), II.2.10, printed p. 70. It gives the
determinant needed in matrix coordinates for ordinary conjugation.
