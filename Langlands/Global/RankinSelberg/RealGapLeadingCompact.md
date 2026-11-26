# Compact span of the real leading Gaussian restriction

This module is the real counterpart of the Library's `ComplexGapLeadingCompact`. Notation as in
`RealGapDualChart` and `RealGapLeadingFourier`; `n = k + q + 1`.

* `packedTail_stack`: an upper packed tail `packedTail Y Z` fixes every `n × k` matrix
  `stack(X, 0)` whose last `q + 1` rows vanish.
* `retainedTail_stack`: `retainedTail p Z · stack(X, 0) = v · stack(S · X, 0)`, where `v` is the
  orthogonal matrix of `p` and `S = leadingScalar y` the scalar of the normalized chart. The triangular
  tail factors fix these columns.

`RealGapLeadingCompactStatement` (proved by `realGapLeadingCompact`): for outer data `p`, `Z` and a
complex polynomial `P` in the entries of `n × k` matrices, the leading square restriction
`Ξ = leadingRestriction k (q+1) k (retainedTail p Z) (gaussianPolynomial P)`, the function
`X ↦ gaussianPolynomial P (retainedTail p Z · stack(X, 0))` of a `k × k` matrix, has a finite-dimensional
span of left translates `X ↦ Ξ(u^{-1} X)` by the orthogonal group `O(k)`.

The scalar `S` commutes with `O(k)`. So the left translate by `u ∈ O(k)` is the left translate of the
rectangular Gaussian by the conjugate `v · diag(u, 1) · v^{-1}` of the embedded orthogonal matrix,
restricted along the linear map `F ↦ (X ↦ F(retainedTail p Z · stack(X, 0)))`. The span of the
left orthogonal translates of a polynomial Gaussian is finite-dimensional
(`RealJacquet.finiteDimensional_gaussianPolynomial_left`), and the embedded matrices are orthogonal
(`RealUnequalPairConvergence.blockSum_mem_unitary`). The finite left orthogonal span is the hypothesis
used by the compact-projection proof of the square step in `RealGapSquareReflection`. In Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), the square step is (10.10) in §10.3, p. 76, which
invokes the matrix functional equation of Proposition 4.4, p. 31.
