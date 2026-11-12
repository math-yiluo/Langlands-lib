# Laurent numerators of scalar Mellin integrals

This helper module is internal infrastructure for the proof of
`Langlands.GodementJacquet.LocalTateConductorStatement`. It packages the shell
expansion from `LocalTateMellin` as a Laurent polynomial identity, and derives
the rational continuation of each Mellin integral from it.

Throughout, `η : Fˣ →* ℂˣ` is a continuous character with exact unit conductor
`a`, `X_s = q^{-s}`, and `Z(Φ, η, s)` is the actual weight-one
`scalarMellinIntegral` against `localMultiplicativeHaar F`.

## Euler polynomial

`eulerPoly η a` is `1 - η(ϖ) X` if `a = 0` and `1` otherwise. This is exactly
the polynomial `P` (for `η = χ`) or `PDual` (for `η = χ⁻¹`) of the target
statement. Its constant coefficient is one, it is nonzero, and it does not
vanish at `x` when `‖η(ϖ) x‖ < 1`.

## The predicate `HasLaurentMellin`

`HasLaurentMellin η P Φ ℓ` holds when there is a real `σ` such that, for every
`s` with `σ < Re s`:

- the Mellin integrand of `Φ` is integrable;
- `P(X_s) · Z(Φ, η, s) = laurentEval (spectralUnit s) ℓ`, the value of the
  Laurent polynomial `ℓ` at `X_s`.

Its closure properties are:

- `hasLaurentMellin_zero`, `hasLaurentMellin_add` and `hasLaurentMellin_smul`:
  it is closed under the zero function, sums and complex scalar multiples, with
  the matching operations on `ℓ`. Sums use the larger of the two thresholds.
- `hasLaurentMellin_dilate`: if `Φ` has Laurent numerator `ℓ`, then
  `Φ(b ·)` has `η(b)⁻¹ T^{-ord b} ℓ`. Substitute `x ↦ b x`, which preserves
  `localMultiplicativeHaar F` (`integral_mul_left_eq_self`). Then use
  `abv(b x)^s = abv(b)^s abv(x)^s` for nonnegative reals and
  `abv(b)^s = X_s^{ord b}`.

## Explicit numerators

`shellLaurent η a Φ A M` is

`P · ∑_{k=A}^{M-1} η(ϖ)^k shellCoeff η Φ k T^k + Φ(0) [a = 0] η(ϖ)^M T^M`,

where `P = eulerPoly η a`. `hasLaurentMellin_shellLaurent` proves
`HasLaurentMellin η P Φ (shellLaurent η a Φ A M)` with threshold
`σ = log_q ‖η(ϖ)‖`. Here `Φ` vanishes outside `ϖ^A O` and is constant on
`ϖ^M O`. The proof substitutes the closed form `mellin_eq`. When `a = 0`, the
factor `1 - η(ϖ)X_s` cancels the geometric tail. When `a ≥ 1`, the tail is
already zero. `exists_hasLaurentMellin` applies this to every Schwartz--Bruhat
function. `integrable_mellinIntegrand` records that the single half-plane
`Re s > log_q ‖η(ϖ)‖` gives absolute convergence for every test function.

## Rational continuation

`hasRationalContinuation_of_hasLaurentMellin`: if
`HasLaurentMellin η P Φ ℓ`, the rational function `ℓ / P` is a
`HasRationalContinuation` of `Z(Φ, η, ·)`. Write `ℓ = T^{-n} p` with `p` a
polynomial (`LaurentPolynomial.exists_T_pow`), so that `ℓ / P = p / (X^n P)`.
On the half-plane where `‖η(ϖ)X_s‖ < 1`, the denominator `X_s^n P(X_s)` is
nonzero. The published `regular_and_eval_div` then gives regularity and the
value `p(X_s)/(X_s^n P(X_s)) = Z(Φ, η, s)`.

`laurentToRatFunc_eq_of_hasLaurentMellin`: every rational continuation `R` of
such an integral satisfies `ℓ = P · R` as rational functions. This follows from
the published uniqueness `HasRationalContinuation.unique`.

## Provenance

The rationality of Tate's local zeta integrals in `q^{-s}` with denominator
`L(s, η)⁻¹ = P(q^{-s})` is classical. See Tate's thesis (source
`tate-1967-thesis`, §2.4) and the survey cited in
`LocalTateConductorStatement.md`, (3.1.3). The predicate `HasLaurentMellin` is
an internal device of this proof, not a Library interface or a source
definition.
