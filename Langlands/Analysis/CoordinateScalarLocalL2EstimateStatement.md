# Local scalar L² estimate with all lower order tensors

`Langlands.Analysis.CoordinateScalarLocalL2EstimateStatement d r`
states a local estimate for the actual published
`CoordinateScalarOperator` on `V = EuclideanSpace ℝ (Fin d)` when its
basis is the canonical orthonormal basis
`e = EuclideanSpace.basisFun (Fin d) ℝ`, that is `D.basis = e.toBasis`.
The operator keeps every order from zero through `r`, and its full
`action` is used unchanged.

## Hypotheses

- Every actual coefficient `D.coefficient k w`, for every order
  `k : Fin (r + 1)` and every ordered word `w : Fin k → Fin d`, is
  continuous on an open set `S ⊆ V`.
- The center `x₀` belongs to `S`, and `c > 0` is a real number.
- At the center, the real-frequency homogeneous top coefficient
  polynomial satisfies, for every `ξ : V`,

  `c · ‖ξ‖^r ≤ ‖∑ w : Fin r → Fin d, D.coefficient (Fin.last r) w x₀ · ∏ j : Fin r, (ξ (w j) : ℂ)‖`.

  The polynomial contains no factor of `i` or `2π`. This is the
  hypothesis of the published
  `Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement d r`
  for the frozen array `w ↦ D.coefficient (Fin.last r) w x₀`.

No uniform coefficient or symbol bound on a neighborhood, no
perturbation estimate and no compact-support premise is assumed.

## Conclusion

For an order `m` write the ordered derivative tensor norm

`TₘF(x) = sqrt(∑ w : Fin m → Fin d, ‖(iteratedFDeriv ℝ m F x) (e (w 0), …, e (w (m-1)))‖²)`.

Every ordered word, including repeated letters, is counted once, so
the exact ordered multiplicities are kept.

There exists `R > 0` with `closedBall x₀ R ⊆ S`. The radius is chosen
before the test function. For every `F : V → ℂ` with `ContDiff ℝ ∞ F`
and `tsupport F ⊆ closedBall x₀ R`,

`eLpNorm (TᵣF) 2 volume ≤ ofReal (2 · c⁻¹) · (eLpNorm (D.action F) 2 volume + ∑ k : Fin r, ofReal ((∑ w : Fin k → Fin d, ‖D.coefficient k.castSucc w x₀‖) + 1) · eLpNorm (TₖF) 2 volume)`.

Here `k.castSucc` is the order `k < r` viewed in `Fin (r + 1)`, so the
sum runs over every lower order term of the operator. The weight of the
order `k` term is the whole coefficient sum over all words of length
`k` at `x₀`, plus one added once, not once per word. All norms are
extended `L²` norms for the canonical `volume`; no infinite value is
replaced by its real projection. Here `∞` is the smooth order from the
scoped `ContDiff` notation, not the analytic order `ω`. A function
supported in the closed ball has compact support because the actual
Euclidean closed ball is compact, so no separate compact-support
premise is needed. The names `Tₘ` above only explain the displayed
expressions; the Lean file exports no separate definitions for them.

## Provenance and intended argument

This is an internal derived statement motivated by coefficient
freezing in the scalar elliptic route. No separate original literature
theorem is attributed to it. Its elementary provenance is continuity
of finite coefficient sums, the constant coefficient Fourier estimate
of `ConstantCoefficientEllipticL2EstimateStatement`, absorption of a
top coefficient difference of total size at most `c / 2` as in the
published `Langlands.Analysis.PrincipalCoefficientPerturbationL2Statement`,
and the `L²` triangle inequality for every retained lower order term.

The intended proof runs as follows. Continuity at `x₀` gives one closed
ball inside `S` on which
`∑ w, ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖ ≤ c / 2`
and on which, for each `k < r`, the lower coefficient sum
`∑ w, ‖D.coefficient k.castSucc w x‖` is at most its center value plus
one. The perturbation absorption bounds the `L²` norm of `TᵣF` by
`2 · c⁻¹` times the `L²` norm of the top order part of the action.
Writing that part as the full action minus the lower order parts, the
triangle inequality and the pointwise bound of each lower order part by
its coefficient sum times `TₖF` give the displayed estimate.

The triangle inequality for extended norms needs measurability. Each
coefficient-weighted derivative is continuous on `tsupport F`, because
`tsupport F ⊆ S`, `S` is open and the coefficients are continuous on
`S`; off `tsupport F` it is locally zero. Hence it is continuous, so
the extended norm estimates do not omit a measurability obligation.

The Lean file defines only this proposition. None of the steps above,
neither the radius choice, the Fourier estimate nor the absorption, is
proved here.

## Degenerate cases and scope

All dimensions and orders, including zero, are retained. For `r = 0`
the lower order sum is empty, the top polynomial is the single
coefficient at the empty word, and `T₀F = ‖F‖`. For `d = 0` and
`r > 0` there are no words of length `r`, so the top polynomial and
`TᵣF` are zero.

The statement neither changes the norm on a general space nor proves a
coordinate transport from one. Interpolation, cutoffs, radius-gap
factors, factorial bounds, analyticity and automorphic growth are
separate obligations.

Worker 94 authored the statement and the initial exposition. Worker 881
revised the exposition for publication.
