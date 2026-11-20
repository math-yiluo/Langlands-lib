# Compact integration of vector-valued smooth manifold families

This module is an internal analytic prerequisite. It shows that compact
averages of smooth families can be differentiated under the integral sign. It
is needed before derivative-topology density can be proved at a fixed finite
level (Task 7293).

## The statement

`Langlands.Analysis.CompactManifoldVectorIntegralStatement` quantifies over
the following data:

- a compact topological space `X` with a measurable structure that is its Borel
  structure (`BorelSpace X`), and a finite measure `μ` on `X`;
- a smooth real manifold `M` modelled on a finite-dimensional real normed space
  `V` without boundary (`ChartedSpace V M`, `IsManifold 𝓘(ℝ, V) ∞ M`);
- a smooth real manifold `N` modelled on an arbitrary real normed space `H`
  without boundary. `H` need not be finite-dimensional or complete;
- a complex Banach space `E` (`NormedSpace ℂ E`, `CompleteSpace E`). Its
  smooth structure is the real one through restriction of scalars;
- a continuous scalar weight `a : C(X, ℂ)`, a continuous map `j : C(X, N)`
  and a map `h : M × N → E` that is jointly `C^∞` for the product model
  `𝓘(ℝ, V).prod 𝓘(ℝ, H)`.

From these data it concludes four things:

1. for every `p : M`, the function `x ↦ a x • h (p, j x)` is Bochner
   integrable for `μ`;
2. `p ↦ ∫ x, a x • h (p, j x) ∂μ` is `ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞`, which is
   genuine manifold smoothness;
3. for every `p`, the actual manifold derivative
   `mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => ∫ x, a x • h (q, j x) ∂μ) p` equals the
   Bochner integral, in `V →L[ℝ] E`, of
   `x ↦ a x • mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => h (q, j x)) p`;
4. the evaluated form of 3: for every `p` and every model vector `v : V`,
   the derivative of the integral applied to `v` equals
   `∫ x, a x • mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => h (q, j x)) p v ∂μ`.

Mathlib types the tangent spaces as `TangentSpace 𝓘(ℝ, V) p` and
`TangentSpace 𝓘(ℝ, E) _`. These are definitionally `V` and `E`. The
statement uses `show V →L[ℝ] E from …` and `show E from …` only to give the
integrands these vector types, so that the Bochner integral is taken in the
fixed spaces `V →L[ℝ] E` and `E`. The ascriptions change no term. The six
universe parameters `uX uV uM uH uN uE` are independent, and the statement
fixes none of them.

The theorem `Langlands.Analysis.compactManifoldVectorIntegral` proves the
statement in every universe. It depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## The proof

The supporting lemmas live in the namespace
`Langlands.Analysis.CompactManifoldVectorIntegral`.

**Compact uniform derivative bound and dominated differentiation.**
`hasFDerivAt_integral` works with an open set `s` in the finite-dimensional
space `V`. It assumes a family `F : V → X → E` and a proposed partial
derivative `D : V → X → V →L[ℝ] E`, both jointly continuous on `s ×ˢ univ`,
with `D q x` the Fréchet derivative of `q ↦ F q x` at every `q ∈ s`. The
conclusion is that `q ↦ ∫ x, F q x ∂μ` has Fréchet derivative
`∫ x, D p x ∂μ` at each `p ∈ s`. Because `V` is finite-dimensional, a closed
ball around `p` inside `s` is compact. Its product with the compact `X` is
compact, so `‖D‖` has a uniform bound `C` there. The constant `C` is
integrable because `μ` is finite. Continuous functions on the compact space
`X` are integrable, which gives measurability and integrability of `F` and
`D`. Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le` then gives
the conclusion.

**Smoothness of the partial derivative.** `contMDiffOn_partialFDeriv` shows
that `(q, n) ↦ fderiv ℝ (fun q' => h (q', n)) q` is jointly `C^∞` on
`s ×ˢ univ` with values in `V →L[ℝ] E`. The proof applies Mathlib's
`ContMDiffAt.mfderiv` to a family of maps. Tangent coordinates are trivial
for a vector source and a vector target
(`inTangentCoordinates_model_space`, `mfderiv_eq_fderiv`).

**First derivative of the weighted integral.**
`hasFDerivAt_weightedIntegral` applies `hasFDerivAt_integral` to
`F q x = a x • h (q, j x)` and `D q x = a x • fderiv ℝ (fun q' => h (q', j x)) q`.
Joint continuity comes from the continuity of `a`, `j`, `h` and the partial
derivative. The weight does not depend on the parameter, so continuity of
`a` is all that is needed.

**Directional induction at a fixed vector codomain.**
`contDiffOn_weightedIntegral_nat` proves `ContDiffOn ℝ n` for every natural
number `n` by induction on `n`. The codomain stays `E` throughout, and `h`
is universally quantified in the induction. For the step it uses
`contDiffOn_succ_of_fderiv_apply`. For each direction `v`, the derivative
of the integral applied to `v` is the integral of
`x ↦ a x • fderiv ℝ (fun q => h (q, j x)) p v`, by
`ContinuousLinearMap.integral_apply`. The integrand is the weighted compact
restriction of the jointly smooth `E`-valued family
`(q, n) ↦ fderiv ℝ (fun q' => h (q', n)) q v`, so the induction hypothesis
applies to it. Codomains of iterated derivatives never grow, so no universe
lifting is needed. `contDiffOn_weightedIntegral` combines all finite orders
into `C^∞`.

**Local source-chart reduction.** `contMDiff_weightedIntegral` composes `h`
with the inverse extended chart of `M` at `p` on the first factor. The
composite is jointly smooth on `chart target ×ˢ univ`, which is open in `V`
because the model has no boundary. The vector-parameter result applies to
this composite. `contMDiffAt_iff_source` then turns smoothness in the chart
back into manifold smoothness at `p`. No chart, smoothness or
differentiability of `j` or of `a` is used.

**Identifying genuine derivatives.** `mfderiv_eq_fderiv_chart` shows the
following. For a map `M → E` that is manifold-differentiable at `p`, its
`mfderiv` at `p` is the ordinary `fderiv` of the map read in the source
chart, at the chart image of `p`. This holds because the model has no
boundary and the target is a vector space. `mfderiv_weightedIntegral` uses
this on both sides. On the left it applies to the integral, which is smooth
by the previous step. On the right it applies to each slice
`q ↦ h (q, j x)`. The first-derivative formula in the chart
(`hasFDerivAt_weightedIntegral`) then gives conclusion 3.
`mfderiv_weightedIntegral_apply` gives conclusion 4. Joint continuity of
the chart partial derivative over the compact `X` makes the derivative maps
integrable. `ContinuousLinearMap.integral_apply` then moves evaluation at
`v` through the integral. Conclusion 1 holds because the integrand is
continuous on the compact space `X` and `μ` is finite.

## Provenance and scope

This is an internal development, derived only from Mathlib's differential
calculus on manifolds and its dominated differentiation theorem. No external
source is translated. It extends Worker 779's shared draft for Task 7699
(revision 1) by adding the evaluated identity as a conjunct of the statement.

The published `Langlands.Analysis.CompactManifoldWeightedIntegralStatement`
(module `Langlands.Analysis.CompactManifoldWeightedIntegralStatement`) is a
different result. There the jointly smooth kernel `h : M × N → ℂ` is scalar.
The Banach-valued weight `w : C(X, E)` is fixed and does not depend on the
parameter. It assumes `T2Space X`, allows an infinite-dimensional first model
`V`, and asserts only integrability and smoothness, with no derivative
identity. Here the integrand `h : M × N → E` itself takes Banach values and
varies with the parameter, the weight is a scalar `a : C(X, ℂ)`, `X` need not
be Hausdorff, and `V` must be finite-dimensional. Finite dimension of `V` is
what gives the compact closed ball for the uniform bound. In return, the
statement here identifies the genuine manifold derivative, both as a
continuous linear map and after evaluation. The published statement covers
infinite-dimensional first models, which this one does not. This one asserts
derivative identities, which the published one does not. Neither statement
is used in the other's proof.

The module asserts nothing about compact-finite density, an actual cuspidal
realization or globalization, or multiplicity one.
