# Induction commutation for the matrix Aubert operator over any local field

`Langlands.Aubert.General.RationalPointFamily.GL.LocalFieldMatrixInductionCommutationStatement`
asserts that normalized induction from a standard product Levi intertwines
the unadjusted Aubert operator on that Levi and on the ambient `GL_n`.
The equality holds as an equality of integer-linear maps on the exact
Grothendieck groups of actual smooth finite-length complex representations.
The proposition quantifies over every `LocalFieldData`, every rank including
zero, and every ordered block shape of that rank. It supplies the
finite-length and short exact sequence preservation witnesses for the maps.

The ambient operator is `localFieldMatrixAlternatingOperator`.
Its term for a block shape `C` has coefficient `(-1)^(n - C.length)`.
The Levi operator `localFieldMatrixRefinedAlternatingOperator` sums
normalized induction after normalized Jacquet restriction for each
refinement `S` of the ordered block shape `B`. Its sign is
`(-1)^(sum i, B.size i - (S i).length)`, with the subtraction inside the
sum. Both functors use the actual matrix groups and the reciprocal
half-modulus conventions for induction and Jacquet restriction.

The source is Aubert, *Dualité dans le groupe de Grothendieck des
représentations lisses de longueur finie d'un groupe réductif p-adique*,
Trans. Amer. Math. Soc. 347 (1995), Definition 1.5 and Theorem 1.7(2),
first equality, printed p. 2181. The standard Levi of `GL_n` has one
simple root for each adjacent pair within a block. Counting those roots in
the ambient and refined block shapes gives the two exponents above. The
rank-zero case has the empty shape and the trivial group.
