# Exponential parameters of continuous archimedean characters

Internal support for the actual Hecke functional equation. The theorem
`exists_exp_mul_of_continuous_add` proves that a continuous nonzero complex-valued
multiplicative function on the additive real line, with value one at zero,
has the form `x ↦ exp(c*x)` for a complex constant `c`.

The implemented proof lifts the function through the complex exponential covering,
with the lift fixed to zero at zero. The two lifts of its addition law agree by
uniqueness of covering lifts on the connected real plane, so the lift is additive.
Continuity then makes that additive lift real linear, and its value at one is the
required coefficient.

`exists_circle_exp_mul_of_continuous_add` repeats this argument through the circle
exponential covering, yielding a real coefficient. Here `Circle.exp t` means
`exp(t*i)`, with no `2*pi` in its argument.
`exists_circle_exp_re_im_of_continuous_add` applies that real-line theorem to the
real and imaginary axes and uses additivity to obtain
`f z = Circle.exp (a*z.re + b*z.im)`. These two results include the trivial
character and make no nonzero-frequency assertion.

`exists_zpow_of_continuous_circle_mul` proves that a continuous nonzero
complex-valued multiplicative function on the circle, taking one to one, equals
`z ↦ (z : ℂ)^n` for an integer `n`. Pulling the function back through
`Circle.exp` gives the complex exponential formula of the first theorem.
Its period `2*pi` and the kernel formula for the complex exponential force the
coefficient to be `n*i`. Surjectivity of the circle exponential then proves the
integer-power formula on every point of the circle.

The definitions `complexExponentialParameter`, `circleExponentialParameter` and
`circleCharacterWeight` select the corresponding proved coefficients by
classical choice. Their `_spec` lemmas expose the formulas used to construct
subsequent local character presentations; no uniqueness or effective computation
is asserted.

These are internal derived helpers, proved directly from Mathlib's covering,
exponential-kernel and real-linear homomorphism results. No external
character-classification theorem or global functional equation is assumed.
Transport to the actual infinite completions, the nontriviality of their additive
restrictions, the polar presentations of quasicharacters, and the analytic
conclusions of the global Hecke target remain separate obligations.
