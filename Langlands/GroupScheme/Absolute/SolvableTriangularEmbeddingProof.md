# The Lie–Kolchin closed embedding into the upper triangular group scheme

Worker 277 and Worker 1485.

`solvableTriangularEmbeddingStatement : SolvableTriangularEmbeddingStatement.{u}` proves
the published statement of the same name for an arbitrary universe `u`. Let `H` be a
smooth connected affine group scheme over an algebraically closed field `k : Type u`.
If `H` is solvable as a group scheme, there are `N` and a closed subgroup embedding of
`H` into the concrete upper triangular group scheme. That group scheme is the block
parabolic `GeneralLinear.blockParabolicScheme (Fin N) k (fun i => -(i.val : ℤ))`.

The proof combines two theorems:

- `lieKolchinRationalTriangularization`
  (`Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularization`, Worker 277)
  proves the helper proposition `LieKolchinRationalTriangularizationStatement`. Every
  matrix representation of such a group with solvable rational points becomes upper
  triangular at all rational points after conjugation by one rational point of the
  general linear group. It rests on the abstract Lie–Kolchin theorem for groups with
  separately continuous laws in `Langlands.Group.LieKolchin.DerivedConnected`,
  `Langlands.Group.LieKolchin.CommonEigenvector` and
  `Langlands.Group.LieKolchin.Triangularization`.
- `solvableTriangularEmbedding_of_rationalTriangularization`
  (`Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingReduction`, Worker 1485)
  derives the target from that helper proposition. It takes a closed linear embedding
  from the published `affineLinearEmbeddingStatement`. It passes from geometric to
  rational-point solvability with `IsSolvableGroupScheme.rationalPoints`, conjugates the
  embedding to rational upper triangular form, and uses reducedness of the smooth group
  to factor the conjugated embedding through the block parabolic as a closed immersion.

The theorem is the application of the second to the first. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

This is J. S. Milne, *Algebraic Groups* (2017), Theorem 16.30 (Lie–Kolchin),
printed p. 334, in the closed-embedding form of Proposition 16.2(c), printed pp. 324–325
(`milne-2017-algebraic-groups`). The Markdown of the modules above compares each step
with the source.
