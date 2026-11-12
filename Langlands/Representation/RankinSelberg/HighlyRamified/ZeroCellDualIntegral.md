# The corank-one integral of a translated zero-cell function

Module `Langlands.Representation.RankinSelberg.HighlyRamified.ZeroCellDualIntegral`.

## Statement

`zeroCell_translate_corankOne F n`: over a p-adic field `F` with its canonical topology,
valuation and Borel structures, let `μ` be a compatible quotient measure on
`N_(n+1) \ GL_(n+1)(F)`, `ϖ` a uniformizer and `ψ` an additive character trivial on `O`.
Let `W` be a `ψ`-Whittaker function on `GL_(n+2)(F)` that agrees with the zero-cell
function `W₀ = zeroCellWhittaker hϖ hψ (n + 1)` on the mirabolic subgroup (last row
`(0, …, 0, 1)`). Let `X` be an inverse `ψ`-Whittaker function on `GL_(n+1)(F)` that is
right `GL_(n+1)(O)`-invariant with `X(1) = 1`, and let `a ∈ GL_(n+1)(F)` and `κ ∈ ℂ` satisfy
`X(g a⁻¹) = κ X(g)` for all `g`. Then for every `s ∈ ℂ` the corank-one integrand of the
right translate of `W` by `diag(a, 1)` against `X` is integrable, and

`∫ W(diag(g a, 1)) X(g) |det g|^(s - 1/2) dμ(g) = κ · |det a⁻¹|^(s - 1/2)`.

The statement uses the Library's `corankOneIntegrand`, `corankOneIntegral`,
`translateWhittaker`, `rankInclusion 1` and `determinantWeight` with the normalized
absolute value, exactly as in the JPSS integrals of the gamma relation.

## Proof

Writing `h = g a`, the integrand at the coset of `g` is
`W₀(diag(h, 1)) · κ X(h) · |det h|^(s - 1/2) · |det a⁻¹|^(s - 1/2)`, because `diag(h, 1)` lies in
the mirabolic subgroup (`rankInclusion_lastRow`), `X(g) = κ X(g a)` by the hypothesis
applied to `g a`, and `determinantWeight` is multiplicative
(`Conductor.determinantWeight_mul`). So the integrand is the constant
`κ |det a⁻¹|^(s - 1/2)` times the zero-cell integrand composed with right translation by `a`
on the quotient (`rightTranslate_mk`). Right translation preserves the compatible
quotient measure (`IsCompatible.right_invariant`) and is a measurable embedding, so
integrability and the integral transfer from the zero-cell integrand, whose integral is
`1` for every `s` by the Library theorem `integrable_integral_corankOneIntegrand_zeroCell`.

## Use

This computes, in closed form, the dual side of the corank-one functional equation in the
proof of the level of the zero-cell Kirillov lift (JPSS 1981, proof of Theorem (5.1)(ii)):
the dual function of the comparison vector is the translate by `diag(ϖ^m, …, ϖ^m, 1)` of a
zero-cell lift for the inverse-transpose representation, and `X` is the dual of a spherical
test function, on which the central scalar `ϖ^(-m)` acts by a scalar.
