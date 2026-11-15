# The largest proper submodule of a strictly dominant principal series

Lean module: `Langlands.Representation.Archimedean.StrictPrincipalSeriesQuotient`.

Let `χ` be a strictly dominant signed power on `GL_n(ℝ)` with signs `χ_l(−1) = (−1)^{p_l}`.
This module shows that the `O(n)`-finite principal series `X(χ)` has a largest proper
`(𝔤, K)`-stable subspace (`isProperGKStable_largestProper`).

Declarations without a prefix are in the namespace
`Langlands.Archimedean.StrictPrincipalSeriesQuotient`.

## Definitions

* `IsGKStable n χ W`: `W ≤ X(χ)`, and `W` is stable under right translation by `O(n)` and under
  the right derivatives `R(X)`, `X ∈ 𝔤𝔩_n(ℝ)`.
* `IsProperGKStable n χ W`: `IsGKStable n χ W`, and some `f ∈ X(χ)` is not in `W`.
* `largestProper n χ` is the supremum of all proper `(𝔤, K)`-stable subspaces.

## Results

* `le_largestProper` and `largestProper_le` are immediate.
* `isGKStable_largestProper`: the supremum is `(𝔤, K)`-stable. The proof uses
  `Submodule.iSup_induction`. Right translation is additive. Right derivatives are additive on
  smooth functions (Library `rightDerivative_add`), so the induction carries membership in
  `X(χ)` along.
* `isProperGKStable_largestProper`: the supremum is proper, and it lies in the kernel of the
  Jacquet integral. Every proper `W` lies in `JacquetKernel.jacquetKernel`
  (`JacquetKernel.jacquet_eq_zero_of_proper`), so the supremum does too. Some `f ∈ X(χ)` has
  `Λ_n f ≠ 0` (`JacquetNonvanishing.exists_jacquet_ne_zero`), so `f` is not in the supremum.
