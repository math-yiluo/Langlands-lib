# A connected solvable group is a unipotent subgroup times a torus centralizer

`Langlands.GroupScheme.solvableTorusCentralizerProduct.{u}` proves the
published `SolvableTorusCentralizerProductStatement.{u}` for the supplied
representative `c : C ⟶ G` of the centralizer. [Statement](SolvableTorusCentralizerProductStatement.md)

Smoothness supplies local finite type, so
`exists_maximalTorus_extension_of_finiteType` extends the closed torus
`j : T.toGrp ⟶ G` to a maximal torus `m : M.toGrp ⟶ G` with a
factorization `f ≫ m = j`. The image of `M` commutes with the image of `T`
on every test scheme since `M` is commutative. The representing property
of `c` therefore gives `factor : M.toGrp ⟶ C` with `factor ≫ c = m`.
[Maximal-torus extension](../Rational/MaximalTorusFiniteType.md) ·
[Centralizer containment](../Rational/MaximalSplitTorusCentralizer.md)

`solvableMaximalTorusSemidirect` gives a closed unipotent subgroup
`i : U ⟶ G` for which `subgroupMultiplication i m` is an isomorphism of
schemes over the field. The identity on `U` and `factor` induce a map
`U × M → U × C` whose composite with `subgroupMultiplication i c` is
`subgroupMultiplication i m`. The composite is surjective on underlying
topological spaces, so `subgroupMultiplication i c` is surjective. [Solvable semidirect product](SolvableMaximalTorusSemidirectProof.md)

The source is J. S. Milne, *Algebraic Groups* (Cambridge University Press,
2017), registered as `milne-2017-algebraic-groups` with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The conclusion is the product clause of Theorem 16.41, printed p. 339.
The Lean proof uses the maximal-torus decomposition of Theorem 16.33(d),
printed p. 336. [Chapter 16](https://www.cambridge.org/core/books/abs/algebraic-groups/structure-of-solvable-algebraic-groups/DF12A81A5F6FC570B903557513460F68)
