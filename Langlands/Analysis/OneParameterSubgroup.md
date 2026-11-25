# Continuous one-parameter subgroups of a Banach algebra

The module `Langlands.Analysis.OneParameterSubgroup` proves that a continuous one-parameter subgroup
of a complete normed `ℝ`-algebra is an exponential.

## Content

`Langlands.exists_exp_smul_of_continuous_oneParameter`: if `m : ℝ → A` is continuous, `m 0 = 1` and
`m (s + t) = m s * m t`, then `m t = exp (t • X)` for some `X ∈ A`. For small `ε > 0` the integral
`B = ∫₀^ε m` is invertible (it is close to `ε`); the identity `m t B = ∫_t^{t+ε} m` makes `m`
differentiable with `m' = m X`, `X = (m ε - 1) B⁻¹`; then `m t · exp (-t X)` has derivative `0`, hence
is constant. Used in `Theta/Real/Metaplectic/Smooth` for one-parameter groups of matrices and of
scalars.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/CartanFactorisation/EqOfInner.lean`, lines 12–59
(`exists_exp`). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `PositivityTheory.ThKF.E.exists_exp` → `Langlands.exists_exp_smul_of_continuous_oneParameter`;
  `letI` replaced by `let` in the proof. Otherwise the source's text.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- theorem `Langlands.exists_exp_smul_of_continuous_oneParameter`

## Dependencies

Mathlib only: `Analysis.Calculus.Deriv.Shift`, `Analysis.Calculus.MeanValue`,
`Analysis.LocallyConvex.AbsConvexOpen`, `Analysis.SpecialFunctions.Exponential`,
`MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`.
