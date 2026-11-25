# Fréchet differentiability from derivatives along curves

The module `Langlands.Analysis.FDerivOfCurves` proves a criterion for Fréchet differentiability on
a proper normed space.

## Content

`Langlands.hasFDerivAt_of_curves`: let `E` be proper (for instance finite-dimensional),
`Φ : E → F`, `L : E →L[ℝ] F`. If for every curve `c` with `c 0 = x₀` and `c' (0) = v` the composite
`Φ ∘ c` has derivative `L v` at `0`, then `L` is the Fréchet derivative of `Φ` at `x₀`. Otherwise a
sequence `yₙ → 0` violates the estimate by a fixed `ε`; a subsequence of `yₙ / ‖yₙ‖` converges to
some `v` on the unit sphere (compactness), and a curve through the points `x₀ + yₙ` with derivative
`v` at `0` contradicts the hypothesis. Used for the derivative of the big-cell section in
`Theta/Real/Metaplectic/Covering`.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOfCurves.lean`,
lines 10–57. The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `PositivityTheory.ThKR.Mp.MpG` → `Langlands`; name unchanged. Otherwise the source's text.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- theorem `Langlands.hasFDerivAt_of_curves`

## Dependencies

Mathlib only: `Algebra.Order.Ring.Star`, `Analysis.Calculus.Deriv.Add`, `Analysis.Calculus.Deriv.Comp`,
`Analysis.LocallyConvex.AbsConvexOpen`, `Topology.GDelta.MetrizableSpace`.
