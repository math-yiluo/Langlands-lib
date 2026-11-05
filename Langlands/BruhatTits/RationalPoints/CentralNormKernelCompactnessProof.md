# Proof of compactness of the full scheme-centre intersection with the rational norm kernel

Authors: Worker 1532 and Worker 1045.

`Langlands.BruhatTits.RationalPoints.centralNormKernelCompactness` proves the Library
proposition `Langlands.BruhatTits.RationalPoints.CentralNormKernelCompactnessStatement.{u}`
(module `Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement`), at an arbitrary
universe `u` and with its hypotheses unchanged. For every nonarchimedean local field `F` and
every `M` with `GroupScheme.IsConnectedReductive M`, the set
`schemeCenterPoints M ⊓ Plancherel.rationalCommonNormKernel M` of rational points is compact in
`rationalPointTopology F M.X`. The centre is the full all-test scheme centre `center M`
(possibly disconnected and nonreduced); no splitness, tameness or characteristic assumption is
made, and both mixed and equal characteristic are covered. The proof uses no split component
of the centre, no quotient `Z(F)/A(F)` and no torus structure of the centre; it bounds matrix
entries directly.

## Proof

1. The published `affineLinearEmbeddingStatement` gives a closed immersion
   `ρ : MatrixRepresentation M (Fin N)` (`M` is affine and, being smooth, locally of finite
   type).
2. **Closedness.** `schemeCenterPoints M` is closed: it is the rational points of the closed
   subgroup representing the centre (`schemeTheoreticCenterExistence_of_isAffineHom`,
   `IsSchemeTheoreticCenter.isRepresentedBy`, `isClosed_rationalPoint_subgroup`). The norm kernel
   is closed (`Plancherel.isClosed_rationalCommonNormKernel`).
3. **Boundedness.** `CentralNormKernel.exists_entry_bound` (module `CentralNormKernel.Bound`),
   applied with `IsConnectedReductive.hasTrivialGeometricUnipotentRadical`, bounds the matrix
   entries of every point of the intersection. Applied to `z⁻¹`, which lies in the same subgroup,
   it bounds the entries of `ρ(z)⁻¹ = ρ(z⁻¹)`.
4. **Compactness.** `CentralNormKernel.isCompact_of_isClosed_of_bounded` (module
   `CentralNormKernel.BoundedCompact`) concludes.

## The bound, in outline

The helper modules under `Langlands/BruhatTits/RationalPoints/CentralNormKernel/` each have their
own Markdown. Over the algebraic closure `K` of `F`:

- the matrices of central rational points of `M_K` generate a commutative finite-dimensional
  algebra, which has complete orthogonal idempotents `E i` and characters `χ i` with
  `(x - χ i x) E i` nilpotent (`Decomposition`, `CentralAlgebra`); each `E i` gives a
  block-determinant character of `M_K`;
- the central rational points with unipotent matrix form a finite set: they lie in the kernel of
  the block characters on the centre, whose points have root-of-unity eigenvalues, and the
  identity component of its reduced subgroup is then unipotent and trivial by the trivial
  geometric unipotent radical (`CentralFiniteness`, `CentralUnipotent`);
- every central rational point `z` is `s u` with `s = ∑ χ i (z) E i` the matrix of a central
  rational point and `u` central with unipotent matrix (`CentralJordan`). That `s` is the matrix
  of a point follows from the lifting criterion for closed immersions (`PointLifting`) and a
  Laurent-polynomial argument on the coordinate ring of `GL_N` (`Laurent`): in characteristic `p`
  from `ρ(z ^ (q k)) = s ^ (q k)` and Vandermonde independence; in characteristic zero from the
  interpolation of `u ^ k` by binomial polynomials and Worker 1045's independence of exponential
  polynomials (`ExponentialPolynomial`);
- for `z` in the norm kernel every eigenvalue has spectral norm `1`, using an `F`-rational block
  character and Worker 1045's `exists_blockProjector_spectralNorm` (`Norm`, `SpectralBlock`);
- the base change of rational points and matrices is in `BaseChange`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
