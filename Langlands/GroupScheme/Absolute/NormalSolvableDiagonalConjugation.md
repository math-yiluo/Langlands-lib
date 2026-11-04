# Diagonal invariance under ambient conjugation

This internal construction continues `SolvableSubgroupTriangularRepresentation`.
Let `k` be any field, let `i : H → G` be a group-scheme homomorphism, and let
`Q` be compatible closed ambient and triangular representations of `i`.
The definition `Q.diagonalHom` is the actual composite from `H` through its
triangular embedding and the concrete block-diagonal projection. Its target
is the block Levi scheme for the distinct weights `j ↦ -j.val`.

The lemma `Q.isUpperTriangular` says that the matrix of every test-scheme
point of `H`, mapped to `G` and then through `Q.ambient`, is upper triangular.
It follows from the scheme-level compatibility in `Q` and the defining
below-diagonal equations of the concrete block parabolic.

Assume that `G` and `H` are smooth, connected and affine over `k`. Let
`a : AutomorphicAction G H` be an actual action whose image under `i` is
ambient conjugation on every test scheme. The theorem
`Q.diagonal_conjugation` proves that this action preserves every diagonal
matrix coefficient on every test scheme. The theorem
`Q.diagonalHom_conjugation` proves equality of the actual diagonal-projection
points before and after the action. No algebraic-closedness or characteristic
restriction occurs in these two statements; the compatible representation
and the actual conjugation action are explicit input data.

The implementation applies `smoothConnectedAffineGeometry` to the universal
product `W = G × H`, making its global-section ring a domain. The universal
subgroup matrix `B` and conjugated subgroup matrix `C` are upper triangular.
Their characteristic polynomials agree because they are conjugate by the
ambient matrix at the universal point of `G`. Pullback by the morphism
`(g,h) ↦ (1,h)` is a ring endomorphism fixing every diagonal coefficient of
`B` and sending each diagonal coefficient of `C` to the matching coefficient
of `B`. The domain lemma
`MatrixRepresentation.diagonal_eq_of_charpoly_of_retraction` then proves
equality of the universal diagonals. Naturality pulls this equality back to
any test scheme. The concrete formula for `blockLimitHom` identifies its
matrix with the diagonal part, so the distinct weights give the equality
of diagonal-projection points.

Finally, `Q.commutator_diagonalHom` shows that the universal point
`a.act(fst,snd) * snd⁻¹` in `H` has trivial diagonal. The definition
`Q.commutatorKernelFactor` constructs its factor through the actual
scheme-theoretic kernel of `Q.diagonalHom`, using `kernelPointsEquiv`.
The theorem `Q.commutatorKernelFactor_comp` identifies its composite with
the kernel inclusion with that universal commutator in `H`. These are
morphisms of schemes over the field, not just rational-point identities.

The provenance is internal: this argument combines the compatible
representation construction, smooth connected product geometry, Mathlib's
invariance of characteristic polynomials under conjugation, and the actual
block-limit and kernel point equivalences. It is a prerequisite for normal
solvable centrality. It does not assert kernel smoothness, kernel
connectedness, normal-solvable centrality or positive-root uniqueness.
