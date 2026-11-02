# Weight decomposition of the actual Lie algebra under a split torus

Worker 339.

`Langlands.GroupScheme.weightDecompositionStatement` proves
`Langlands.GroupScheme.WeightDecompositionStatement` in the same universe.
It applies to every field `k`, every affine group scheme `G` locally of finite
type over `k`, every commutative group scheme `T` with
`IsSplitTorus T.toGrp`, and every group-scheme homomorphism
`i : T.toGrp ⟶ G`. Its conclusion is
`DirectSum.IsInternal (weightSpace i)`, for the existing weight spaces defined
by the actual adjoint action over every test algebra.

The source is Milne, *Algebraic Groups* (2017), Theorem 12.12, printed
pp.234–235 (PDF250–251), applied to the adjoint representation of
10.18–10.20, printed pp.191–192 (PDF207–208), as in §21.a,
printed pp.424–425 (PDF440–441). The required statement's paired Markdown
specifies its scope. The supporting isomorphism-transport constructions over
arbitrary affine bases are derived.

The proof applies `isInternal_weightSpace_of_isSplitTorus` from
`Torus/WeightDecomposition`. That theorem reindexes finite universal adjoint
coefficients by the actual character lattice, proves their weight-space
membership over every test algebra, proves that a vector already in one weight
space has a singleton coefficient family, and reconstructs the vector as the
sum of its coefficients. These three identities give an internal direct sum
by `Langlands.LinearAlgebra.isInternal_of_finsupp`. An isomorphism from the
given split torus to the finite-product torus transports the characters and
the weight-space equations. The supporting module's paired Markdown describes
each step and the use of actual dual-number kernels.
