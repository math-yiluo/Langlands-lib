# Weighted unequal-rank identities on real Whittaker right translates

## Definitions

For `t < r`, functions `W` on `GL_{r+1}(ℝ)`, `V` on `GL_{t+1}(ℝ)` and weights `f : ℝ → ℂ`:

* `weightedOrdinary h W V f q = realUnequalIntegrand h W V 0 q · f (quotientDetAbs q)` on the
  quotient `Q_t`;
* `weightedDual h W V f p = realUnequalDualKernel h W V 0 p · f (quotientDetAbs p.1)` on
  `Q_t × Mat_((r-t-1)×(t+1))(ℝ)`.

## Statement

`RealWhittakerTranslatedIntegralsStatement`: let `B`, `B'` be specified real Whittaker
intertwiners for the characters `a` and `-a`, and `f`, `f'` measurable weights. Assume that

`∫ weightedOrdinary h (B p) (B' p') f = ∫ weightedDual h (B p) (B' p') f'`

for all standard vectors `p`, `p'` (with `D.measure` and `realUnequalDualMeasure a D`). Let `v`,
`v'` be standard vectors and `g`, `g'` group elements, and suppose integrable functions `M`, `M'`
bound the two weighted kernels of the right translates `ρ(k g)(B v)`, `ρ(l g')(B' v')` uniformly in
orthogonal `k`, `l`. Then the same identity holds for the translates `ρ(g)(B v)` and
`ρ(g')(B' v')`.

`realWhittakerTranslatedIntegrals` proves it: `realWhittakerRightTranslateApproximation` gives
values `B (U j)`, `B' (V j)` converging pointwise to the two translates, each a positive unit-mass
compact average of translates, so the bounds `M`, `M'` pass to the approximants
(`norm_compactAverage_pair_le`). The unweighted kernels `realUnequalIntegrand h (B (U j)) (B' (V j)) 0`
and `realUnequalDualKernel h (B (U j)) (B' (V j)) 0` of the approximants are continuous
(`RealUnequalFamily.continuous_integrand`, `continuous_dualKernel`); multiplied by the measurable
determinant weights `f ∘ quotientDetAbs`, `f' ∘ quotientDetAbs` they are a.e. strongly measurable.
Dominated convergence with the integrable majorants `M`, `M'` transports the identity, which holds
for every `j` by hypothesis.

This is the real counterpart of the Library's `ComplexWhittakerTranslatedIntegrals` (whose
hypothesis quantifies over the exact finite Whittaker models); it is used in the larger-gap
recurrence of Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §10.3.
