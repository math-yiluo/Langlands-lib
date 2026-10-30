# Absorption of a small principal coefficient perturbation

`Langlands.Analysis.PrincipalCoefficientPerturbationL2Statement d r`
states an internal perturbation consequence of the published homogeneous
constant coefficient estimate. It keeps the actual Euclidean domain,
canonical volume, ordered standard basis derivative tensor and extended
L² norms.

The constant array `a₀` has a real frequency symbol bounded below by
`c * ‖ξ‖^r`, where `c > 0`. The variable array `a` differs from `a₀`
by a total coefficient norm at most `c / 2` at every point of the
topological support of the given smooth compactly supported function
`F`. The conclusion bounds the complete ordered derivative tensor in
L² by `2 * c⁻¹` times the L² norm of the actual variable principal
action. The array can be frozen at a center by choosing `a₀ w = a w x₀`,
but this statement does not require that particular choice.

The tensor norm is exactly the square root of the sum of squared norms
of `iteratedFDeriv ℝ r F x` evaluated on every ordered standard basis
word. Repeated directions retain their ordered multiplicities. The
opened `ContDiff` scope makes `ContDiff ℝ ∞ F` mean smoothness; literal
`⊤ : ℕ∞ω` would instead impose analytic order.

No regularity or measurability of `a` is assumed. Mathlib's extended
L² norm is infinite for a function that is not almost everywhere
strongly measurable. If the variable action has infinite extended norm,
the conclusion is automatic since `2 * c⁻¹` is positive. In the finite
case its measurability gives measurability of the error by subtracting
it from the smooth constant coefficient action. Smooth compact support
also makes the tensor norm finite, as needed for absorption. Thus
removing coefficient regularity does not authorize subtraction of
infinite extended values.

All dimensions and orders, including zero, are included. The support
condition is imposed only where derivatives can be nonzero:
`support_iteratedFDeriv_subset` places their support inside `tsupport F`.
There is no division by the number of words or a derivative value.

For the intended derivation, write `T(x)` for this tensor norm,
`P₀(x)` for the constant principal action, `P(x)` for the variable
action, and `E(x) = P₀(x) - P(x)` for the error. These are explanatory
names, not additional Lean declarations. Each component norm is at most
`T(x)`, so the triangle inequality and the support-local hypothesis give

`‖E(x)‖ ≤ (∑ w, ‖a₀ w - a w x‖) * T(x) ≤ (c / 2) * T(x)`

on `tsupport F`. Off `tsupport F`, all the derivatives vanish, so the
final bound also holds there without a coefficient hypothesis.
Continuity and compact support make `T` and `P₀` have finite L² norms.
When `P` has finite L² norm, the measurable error discussed above then
satisfies `‖E‖₂ ≤ (c / 2) * ‖T‖₂`. Applying the constant coefficient
estimate to `P₀ = P + E` gives the finite inequality

`‖T‖₂ ≤ c⁻¹ * (‖P‖₂ + (c / 2) * ‖T‖₂)`.

Absorbing the last term gives `‖T‖₂ ≤ 2 * c⁻¹ * ‖P‖₂`. This explains
the exact factor two without subtracting infinite values. All these
steps remain proof obligations for a successor; the present file defines
only the unconditional target proposition and assumes no Fourier estimate.

This is an internal derived statement. Its provenance is the elementary
triangle inequality and absorption step after the published
`ConstantCoefficientEllipticL2EstimateStatement`; it does not transcribe
or quote a separate literature theorem. The coefficient freezing and
small ball step of the Morrey–Nirenberg route motivates its use, but no
local neighborhood, lower order term estimate, cutoff, factorial bound,
analyticity or automorphic growth is asserted here.

Worker 94 authored the statement and initial exposition. Worker 88 checked
the published import and extended-norm conventions and expanded the
absorption explanation for publication.
