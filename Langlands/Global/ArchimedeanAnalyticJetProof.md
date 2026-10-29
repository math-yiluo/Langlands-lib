# Analytic uniqueness on an actual archimedean connected component

This module proves the published statement
`Langlands.Global.ArchimedeanGL.AnalyticMatrixJetUniquenessStatement K n`
from `Langlands.Global.ArchimedeanAnalyticJetStatement`, for an
arbitrary number field `K : Type u` and every natural rank `n`,
including `n = 0`. It imports the statement unchanged and adds only the
theorem `Langlands.Global.ArchimedeanGL.analyticMatrixJetUniqueness`.
The argument was drafted by Worker 94 and checked and submitted by
Worker 990.

## The implemented proof

Fix `f : SmoothFunctions K n`, a basepoint `x₀` of the
completion-based group `GL_n(InfiniteAdeleRing K)`, the analyticity
hypothesis at every unit matrix, and the vanishing of every iterated
real Fréchet derivative at the basepoint's coordinates.

1. **Coordinate image.** Let `q x` be the published coordinates
   `archimedeanGLCoordinates K n x`, viewed as an ambient matrix in
   `ArchimedeanMatrix K n` through the units embedding. Both maps are
   continuous, so the image `S = q '' connectedComponent x₀` is
   preconnected and contains `q x₀`.
2. **Analyticity on the image.** Every point of `S` is the matrix of a
   unit, so the analyticity hypothesis gives
   `AnalyticOnNhd ℝ (coordinateExtension K n f) S`. Analyticity at
   singular matrices is never used.
3. **Local vanishing.** Analyticity at `q x₀` supplies a power series on
   a ball of positive radius. On that ball, Mathlib's
   `HasFPowerSeriesOnBall.hasSum_iteratedFDeriv` writes
   `coordinateExtension K n f (q x₀ + y)` as the sum over `m` of
   `(m!)⁻¹` times the `m`-th iterated real Fréchet derivative at `q x₀`
   applied to the constant tuple `y`. The jet hypothesis makes every
   term zero, the order-zero term included, so uniqueness of sums gives
   zero on a neighborhood of `q x₀`.
4. **Propagation.** The several-variable identity theorem
   `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`
   extends this local zero to all of `S`.
5. **Return to `f`.** For `x ∈ connectedComponent x₀`, the value at
   `q x` is zero; `coordinateExtension_apply` and cancellation of the
   coordinate equivalence with its inverse identify it with `f.val x`.

## Scope

This is an internal specialization of Mathlib's analytic identity
principle to the published archimedean coordinates. It keeps the
published operator norm and topology, complex values, arbitrary
number-field universe, every natural rank and all group components:
the conclusion holds on `connectedComponent x₀` only, and no
connectedness of the group is used. It does not derive analyticity from
smoothness, differential equations or joint finiteness, does not relate
the published enveloping derivatives to ambient jets, and proves no
orbit density, reproduction or automorphic growth statement.
