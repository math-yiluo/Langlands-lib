# Comparing the genuine enveloping jet with the ambient matrix jet

The theorem `envelopingZeroJet` proves the published statement
`EnvelopingZeroJetStatement K n` from
`Langlands.Global.ArchimedeanEnvelopingJetStatement`, for every number
field `K : Type u` and every `n : ℕ`. The statement pair and its
imports remain unchanged. This module imports the published statement
and Mathlib's `Mathlib.Analysis.Calculus.ContDiff.Bounds`. Worker 94
developed the argument as an internal local calculus proof.

Write `x` for the underlying mixed-coordinate matrix of `x₀`, which
lies in the open range of `Units.val`. The implementation proves,
by strong induction on the derivative order `k`, that the order-`k`
iterated derivative at `x` vanishes for the coordinate extension of
every vector `envelopingAction K n a f` in the enveloping orbit
of `f`, simultaneously for all `a`. The target is the case `a = 1`,
via `envelopingAction_one`. At order zero, evaluating the coordinate
extension at `x` returns `(envelopingAction K n a f).val x₀`, which
is zero by the supplied hypothesis.

For one such vector, write `F` for its coordinate extension and
`L(y)` for the continuous real linear map of left multiplication by
the ambient matrix `y`. The function with values in continuous
linear maps

```
D(y) = (fderiv ℝ F y).comp (L(y))
```

is smooth on the open set of units. For each fixed matrix direction
`Y`, put `X = (realLieAlgebraToMatrix K n).symm Y`. On the units,
`D(y)(Y)` agrees with the coordinate extension of the genuine real
directional derivative `smoothDifferential K n X` of that vector
(`smoothDifferential_apply`). By `envelopingAction_real_generator`
and `envelopingAction_mul`, this derivative is again in the orbit:
it is `envelopingAction K n (envelopingGenerator K n (complexify K n X) * a) f`.
For the inductive step from orders at most `r` to order `r + 1`,
the induction hypothesis therefore annihilates the order-`j` jet
of `D(·)(Y)` at `x` for every `j ≤ r` and every `Y`. Commuting
evaluation at a constant `Y` with iterated derivatives then
annihilates the order-`j` jets of the linear-map-valued `D`.

Let `T(y)` be left multiplication by `Ring.inverse y`. This is smooth
at every unit (`contDiffAt_ringInverse`). On the open set of units,
`D(y).comp (T(y)) = fderiv ℝ F y`, since `g * (g⁻¹ * Y) = Y`.
Mathlib's iterated derivative norm bound for a continuous bilinear
map (`ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`),
applied to composition `ContinuousLinearMap.compL`, bounds the
order-`r` jet of this product by a sum whose every summand contains
the norm of an order-`j` jet of `D` with `j ≤ r`; all of these vanish,
so the order-`r` jet of `fderiv ℝ F` at `x` is zero. This step
accounts for every differentiated moving-frame coefficient. The
recursion `iteratedFDeriv_succ_apply_right`, expressing the order
`r + 1` iterated derivative of `F` through the order-`r` iterated
derivative of `fderiv ℝ F`, closes the induction.

Two private helper lemmas implement constant-evaluation detection of
a zero linear-map-valued jet and preservation of a zero truncated
jet by a smooth bilinear product. All comparisons occur on the open
units set; eventual equality transfers iterated derivatives at the
chosen unit to the original coordinate extension. No global
smoothness of that extension is assumed.

This is an internal calculus proof route and uses no analyticity or
finite-dimensional-orbit hypothesis. It retains the actual matrix
norm and topology, arbitrary number-field universe and every
natural rank. Analytic regularity, analytic uniqueness, component
propagation, density, reproduction and final automorphic growth
remain separate obligations.
