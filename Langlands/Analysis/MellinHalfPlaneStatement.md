# Holomorphy of positive-weight Mellin integrals

Authors: Worker 351, with the formulation supplied by Worker 161.

## Statement and exact hypotheses

`Langlands.Analysis.MellinHalfPlaneStatement` is a closed `Prop` definition.
It is universe-polymorphic in `u`, and internally quantifies over every
`X : Type u` with a supplied `MeasurableSpace X`, every measure `μ` on `X`,
every `c : X → ℂ`, every `d : X → ℝ`, and every real shift `κ`.
There are no outer term parameters.

For these data the assumptions are precisely:

- `0 < d x` for every `x : X`;
- `AEStronglyMeasurable c μ`;
- `AEMeasurable d μ`;
- for every real `t > 0`,
  `Integrable (fun x => c x * (d x : ℂ) ^ ((t : ℂ) - (κ : ℂ))) μ`.

The conclusion is

```text
DifferentiableOn ℂ
  (fun s : ℂ => ∫ x, c x * (d x : ℂ) ^ (s - (κ : ℂ)) ∂μ)
  {s : ℂ | 0 < s.re}.
```

The power is Mathlib's `Complex.cpow`, with its principal logarithm; the
integral is the actual `MeasureTheory.integral`, the complex-valued Bochner
integral against the supplied measure. Positivity of `d` keeps every base
on the positive real axis and away from zero. Complex differentiability on
this open half-plane expresses holomorphy there.

The measurable space carries no topology. The measure need not be finite,
sigma-finite, a Haar measure, or a product measure. The shift `κ` is
unrestricted. Neither `c` nor `d` is assumed separately integrable.
Holomorphy, continuation, and a majorant for derivatives are not premises.
The conclusion does not include the boundary line `s.re = 0` or any
continuation beyond the stated half-plane.

This module contains the proposition only. No proof of it, derivative
formula, or additional integrability theorem is supplied here.

## Internal provenance and intended derivation

This is an internal measure-theoretic statement, using the formulation
supplied by Worker 161, rather than a transcription of a literature theorem.
The following is the intended argument for a separate proof successor.
It explains why real-axis integrability supplies the local analytic
estimates without adding them as hypotheses.

For a positive real number `r`, the power convention gives

```text
‖(r : ℂ) ^ (s - (κ : ℂ))‖ = r ^ (s.re - κ),
```

where the power on the right is the real power. Consequently the norm of
the complex integrand at `s` equals its norm at the real parameter `s.re`.
The given real-axis integrability, together with the supplied
measurability, can therefore establish integrability at every point of
the half-plane.

Fix `s₀` with `σ = s₀.re > 0`, and choose `h > 0` with `2*h < σ`.
The wider real endpoints `a = σ - 2*h` and `b = σ + 2*h` are positive.
On a neighborhood satisfying `|s.re - σ| < h`, splitting into
`0 < d x ≤ 1` and `1 ≤ d x` bounds the norm of the integrand by

```text
‖c x‖ * (d x ^ (a - κ) + d x ^ (b - κ)).
```

Each summand is the norm of an integrand at one of the positive real
endpoints, so this bound is integrable.

For fixed `x`, differentiation with respect to the complex parameter
introduces the factor `Complex.log (d x : ℂ)`. Since `d x > 0`, its norm
is `|Real.log (d x)|`. The gap `h` between the neighborhood and the wider
endpoints absorbs this factor: for `r ≥ 1`,
`log r ≤ h⁻¹ * r^h`, while for `0 < r ≤ 1`,
`|log r| ≤ h⁻¹ * r^(-h)`. Thus the derivative norm throughout the same
neighborhood is bounded by the integrable function

```text
h⁻¹ * ‖c x‖ * (d x ^ (a - κ) + d x ^ (b - κ)).
```

Almost-everywhere measurability of `d`, continuity of real logarithm on
the positive axis and the complex exponential, and almost-everywhere
strong measurability of `c` give the measurability needed for the
integrands and their parameter derivatives. Dominated differentiation
then yields complex differentiability at `s₀`. Applying this at every
point of the open half-plane gives the stated conclusion.
These estimates describe the proposed proof route; they are not separate
Lean results in this statement module.

## Pinned API and scope

The declaration is written for environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Mathlib pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435`. The relevant parametric-integral
API was read in
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`:
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` provides dominated
parameter differentiation for an arbitrary measure, including complex
parameters. Its local integrable bound and measurability obligations
must be derived in the proof. The statement imports that API and
`Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean` for the actual power.
No external literature result is cited or needed for this formulation.

The intended Rankin–Selberg applications take `d` to be a positive
normalized determinant absolute value, `c` to be an actual product of
Whittaker functions, and `κ = (k + 1)/2`. Proving the real-axis
integrability and measurability in those applications remains separate
representation-theoretic work. This statement supplies no Whittaker
square-integrability, quotient measure construction, or rational
continuation result. All existing published Lean/Markdown pairs are
preserved.
