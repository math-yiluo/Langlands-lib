# Regularity of holomorphic rational continuations

Author: Worker 351, using the mathematical formulation and argument supplied
by Worker 192 in the task specification.

`Langlands.RankinSelberg.HolomorphicRationalContinuationStatement` is a
Prop-valued internal complex-analysis statement. This pair states the target;
it does not supply a Lean proof.

For every natural number `q > 1`, function `f : ℂ → ℂ`, and rational function
`R : RatFunc ℂ`, the hypotheses are exactly:

- `DifferentiableOn ℂ f {s : ℂ | 0 < s.re}`, expressing holomorphy on the
  open positive half-plane;
- the published relation `HasRationalContinuation q f R`.

The latter relation supplies some real threshold `a` such that, for every
`s` with `a < s.re`, the reduced denominator of `R` is nonzero at
`spectralPoint q s = (q : ℂ) ^ (-s)` and `f s` equals the rational
evaluation there. The threshold can be arbitrary; denominator nonvanishing
on the entire positive half-plane is a conclusion, not a hypothesis.

The conclusion is a conjunction:

1. For every `s` with `0 < s.re`,
   `R.denom.eval (spectralPoint q s) ≠ 0`.
2. For every `z : ℂ` with `0 < ‖z‖` and `‖z‖ < 1`,
   `RationalEvaluation.RegularAt R z`.

The second conclusion uses the existing regularity predicate, which means
`R.denom.eval z ≠ 0` for Mathlib's reduced denominator. Both imported
definitions are used without modification.

## Derived provenance and intended argument

This is an internal consequence of elementary complex analysis and polynomial
coprimality, formulated for the published continuation and regularity APIs.
It is not attributed to a source-specific Rankin–Selberg theorem. The
following explains the mathematical justification and the intended proof
obligation; it is not an assertion that this module implements the proof.

Set `H = {s : ℂ | 0 < s.re}` and write `N = R.num`, `D = R.denom`.
Since `q > 1`, the spectral map is the entire function
`s ↦ exp (-s * log (q : ℝ))`. Thus

\[
g(s)=f(s)D(q^{-s})-N(q^{-s})
\]

is holomorphic on `H`. The continuation hypothesis, including its
denominator nonvanishing condition, allows cross-multiplication and shows
that `g` vanishes on the nonempty open half-plane
`{s | max a 0 < s.re}` contained in `H`. The set `H` is open and convex,
hence connected. The identity theorem therefore gives `g = 0` throughout
`H`. If `D(q^{-s})` were zero at a point of `H`, this identity would force
`N(q^{-s}) = 0` too. Mathlib's reduced numerator and denominator are
coprime (`RatFunc.isCoprime_num_denom`); evaluating a polynomial Bezout
identity at that point contradicts simultaneous vanishing. This proves
the first conclusion by the intended argument.

For the second conclusion, let `0 < ‖z‖ < 1` and take

\[
s=-\frac{\log z}{\log q},
\]

where the numerator is any complex logarithm of `z` (the principal
complex logarithm suffices) and the denominator is the positive real
logarithm of `q`, embedded in `ℂ`. Then
`s.re = -Real.log ‖z‖ / Real.log q > 0` and `q^(-s) = z`.
Only a logarithm at each individual nonzero point is needed; no
holomorphic logarithm on the punctured disk is asserted. This shows that
the spectral map from `H` is onto the punctured unit disk, so the first
conclusion supplies the second. Conversely, every spectral point of `H`
has norm `exp (-s.re * Real.log q)` strictly between zero and one.

The exclusion of zero is necessary. For example, `R(X) = 1/X` and
`f(s) = q^s` meet the hypotheses for `q > 1`, while `R` has a pole at
zero. No conclusion is asserted on the unit circle either.

No representation-theoretic condition, integral convergence assertion,
or normalized-generator assertion occurs in this statement. In particular,
pointwise convergence of a family of integrals alone does not establish
the explicit holomorphy hypothesis; applications must supply that
analytic input separately.
