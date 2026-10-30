# Factorial derivative bounds imply real analyticity

Module `Langlands.Analysis.FactorialDerivativeAnalyticity`, namespace
`Langlands.Analysis`.

Throughout, `E` and `F` are arbitrary real normed spaces
(`NormedAddCommGroup` with `NormedSpace ℝ`), with their own norms. No
completeness or finite dimension is assumed except in the two
coordinate results at the end, where a finite basis of `E` is given.
`D^k f(y)` means Mathlib's `iteratedFDeriv ℝ k f y`, a continuous
`k`-multilinear map `E^k → F`, and `‖·‖` on it is the operator norm.
"Smooth on `U`" means `ContDiffOn ℝ ∞ f U`, with `∞` the smooth
(`C^∞`) level of `ℕ∞ω`, not the analytic level `ω`.

## The definition

`realTaylorSeries f x : FormalMultilinearSeries ℝ E F` is the formal
Taylor series of an arbitrary function `f : E → F` at `x : E`. Its
`n`-th term is

  `realTaylorSeries f x n = (n!)⁻¹ • D^n f(x)`,

recorded by the theorem `realTaylorSeries_apply` (it holds by `rfl`).
The definition uses no hypothesis on `f`. When `f` is not differentiable,
Mathlib's iterated derivative takes junk values, so the series is only
meaningful under the smoothness hypotheses of the theorems below.

## The main theorem

`hasFPowerSeriesOnBall_realTaylorSeries_of_iteratedFDeriv_le_factorial`:
let `r > 0` and real constants `C, M` be given. Suppose `f` is smooth on
the open ball `Metric.ball x r` and

  `‖D^k f(y)‖ ≤ C · M^k · k!` for every `y` in that ball and every `k : ℕ`.

Then

  `HasFPowerSeriesOnBall f (realTaylorSeries f x) x (ENNReal.ofReal ρ)`,
  with `ρ = min (r / 2) (1 / (2 · (|M| + 1)))`.

So the series has radius at least `ρ` and, for every `y` with `‖y‖ < ρ`,
the series `∑ₙ (n!)⁻¹ D^n f(x)(y, …, y)` converges to `f (x + y)`.
The constants `C` and `M` may be arbitrary reals; the hypothesis at
`k = 0` forces `0 ≤ C`, and `M` enters only through `|M| + 1 > 0`.

`analyticAt_of_iteratedFDeriv_le_factorial`: under the same hypotheses
`f` is real analytic at `x` (`AnalyticAt ℝ f x`); the proof uses the
series and radius above as the witness.

`analyticOnNhd_of_iteratedFDeriv_le_factorial`: let `S ⊆ E` be open and
`f` smooth on `S`. Suppose that for every `x ∈ S` there are reals `C, M`
such that, for all `y` in some neighbourhood of `x` and all `k`,
`‖D^k f(y)‖ ≤ C · M^k · k!`. Then `AnalyticOnNhd ℝ f S`: `f` is real
analytic at every point of `S`. The constants may depend on `x`, but a
single pair `C, M` must serve all orders `k` on a neighbourhood of that
point; the hypothesis is not a separate bound for each order.

## The coordinate form

`norm_le_of_basis_word_le`: let `b : Module.Basis ι ℝ E` be a basis with
a finite index type `ι`, and let `T` be a continuous `k`-multilinear map
`E^k → F`. Suppose `0 ≤ B` and `‖T (b (w 0), …, b (w (k-1)))‖ ≤ B` for
every word `w : Fin k → ι`. Then

  `‖T‖ ≤ B · (card ι · ‖b.equivFunL‖)^k`,

where `b.equivFunL : E ≃L[ℝ] (ι → ℝ)` is Mathlib's continuous coordinate
isomorphism, viewed as a continuous linear map, `ι → ℝ` carries the sup
norm, and `‖b.equivFunL‖` is its operator norm for the original norm of
`E`. No norm on `E` is changed.

`analyticOnNhd_of_basis_word_le_factorial`: with `b` as above, `S ⊆ E`
open and `f` smooth on `S`, suppose that for every `x ∈ S` there are
reals `C, M` such that, for all `y` near `x`, all `k` and all words
`w : Fin k → ι`,

  `‖D^k f(y)(b (w 0), …, b (w (k-1)))‖ ≤ C · M^k · k!`.

Then `AnalyticOnNhd ℝ f S`. This is the form matching the ordered-word
convention of `Langlands.Analysis.CoordinateScalarOperator` in the module
`Langlands.Analysis.CoordinateScalarDifferentialOperator`, whose
`CoordinateScalarOperator.action` evaluates `iteratedFDeriv ℝ k F x` on
`fun j => D.basis (w j)` for ordered words `w : Fin k → Fin d`.

The helper theorem `iteratedDeriv_comp_line` is used in the proof: if
`f` is smooth on `Metric.ball x r` and `‖t • y‖ < r`, then the `k`-th
one-variable derivative of `s ↦ f (x + s • y)` at `t` is
`D^k f(x + t • y)(y, …, y)`.

## Proofs

`iteratedDeriv_comp_line` writes `s ↦ f (x + s • y)` as `g ∘ L`, with
`g z = f (x + z)` and the continuous linear map `L s = s • y`. Mathlib's
formula for iterated derivatives within open sets of a composition with
a continuous linear map on the right
(`ContinuousLinearMap.iteratedFDerivWithin_comp_right`) and translation
invariance (`iteratedFDeriv_comp_add_left`) give the claim.

For the main theorem, `|M|` is first replaced by `M₁ = |M| + 1 > 0`. The
bound at `x` gives `‖(n!)⁻¹ D^n f(x)‖ ≤ C · M₁^n`, so each term at `y` is
at most `C · (M₁ ‖y‖)^n`. Since `M₁ ρ ≤ 1/2`, the radius is at least `ρ`
(`FormalMultilinearSeries.le_radius_of_bound`), and for `‖y‖ < ρ` the
term norms are summable by comparison with a geometric series. Summable
norms make convergence of the partial sums enough
(`hasSum_iff_tendsto_nat_of_summable_norm`), so no completeness of `F`
is needed. Along the segment `g(s) = f (x + s • y)`, `s ∈ [0, 1]`, which
stays in `Metric.ball x r` because `ρ < r`, the one-variable derivatives
are `D^k f(x + s • y)(y, …, y)` by `iteratedDeriv_comp_line`. So the
Taylor polynomial of `g` at `0` evaluated at `1` is the `N`-th partial
sum of the series. Mathlib's Lagrange-type bound
`taylor_mean_remainder_bound` with
`‖g^(N+1)‖ ≤ C · M₁^(N+1) · (N+1)! · ‖y‖^(N+1)` on `[0, 1]` bounds the
remainder by `C · (N+1) · (M₁ ‖y‖)^(N+1)`. This tends to zero because
`M₁ ‖y‖ < 1` (`tendsto_self_mul_const_pow_of_lt_one`).

The `AnalyticAt` theorem packages the main theorem. The `AnalyticOnNhd`
theorem takes, at each point, a ball contained both in `S` and in the
neighbourhood where the bounds hold.

`norm_le_of_basis_word_le` expands each argument in the basis,
`v_j = ∑_i c_i(v_j) b_i` with `c = b.equivFun`, and uses multilinearity
(`ContinuousMultilinearMap.map_sum`, `map_smul_univ`):
`T v = ∑_w (∏_j c_{w j}(v_j)) • T (b ∘ w)`. Each coefficient satisfies
`|c_i(z)| ≤ ‖b.equivFunL‖ ‖z‖`, and the product of sums is rewritten as a
sum over words (`Finset.prod_univ_sum`), giving
`‖T v‖ ≤ B ∏_j (card ι · ‖b.equivFunL‖ · ‖v_j‖)`.
`analyticOnNhd_of_basis_word_le_factorial` replaces `C, M` by `|C|, |M|`,
applies this bound to `D^k f(y)` with `B = |C| · |M|^k · k!`, and applies
the previous theorem with constants `|C|` and `|M| · card ι · ‖b.equivFunL‖`.

## Provenance and scope

This is a standard fact of real analysis. It is the final step of
Morrey–Nirenberg 1957, Lemma 2.3 and its Corollary (printed pages
276–277, PDF pages 6–7, registered source
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`).
There, the pointwise factorial bounds (2.7) on all derivatives on a
ball, together with `(p + n + 1)! ≤ C₃ 2^p p!` (with `C₃` independent of `p`), are said to imply that
`u` is analytic, with a Taylor radius at the origin exceeding a constant
depending only on `R` and the constant of the bounds. The source states
this implication without proof. The Lean theorems are a derived version
for an arbitrary real normed domain: the bounds are on operator norms of
iterated Fréchet derivatives, or on their values along basis words, and
the radius `min (r / 2) (1 / (2 (|M| + 1)))` is explicit. They do not
contain the Sobolev step (Lemma 2.2), any L² estimate, or any statement
about differential equations.

In the pinned Mathlib (commit `5ed29652`), analyticity follows from
differentiability for complex-differentiable functions
(`DifferentiableOn.analyticAt`, `Mathlib/Analysis/Complex/CauchyIntegral.lean`),
and the Taylor-series results of
`Mathlib/Analysis/Calculus/IteratedDeriv/ConvergenceOnBall.lean` assume
analyticity already. A search found no theorem there deriving real
analyticity from factorial bounds on derivatives, so this unit supplies it.
