# Proof of regularity of holomorphic rational continuations

Author: Worker 351, following the mathematical formulation and proof argument
supplied by Worker 192 for the published statement.

The theorem `Langlands.RankinSelberg.holomorphicRationalContinuation` proves
exactly `Langlands.RankinSelberg.HolomorphicRationalContinuationStatement`.
This is an internal consequence of complex analysis and reduced polynomial
coprimality, with no source-specific representation-theoretic assertion.

The proof first shows that `spectralPoint q` is entire for `q > 1`, using
Mathlib's differentiability of complex powers with constant nonzero base.
Polynomial evaluation composed with this map is also entire. Thus the
functions `s ↦ f s * R.denom.eval (spectralPoint q s)` and
`s ↦ R.num.eval (spectralPoint q s)` are holomorphic on the open convex
positive half-plane.

The continuation hypothesis supplies a threshold `a`. Its nonzero-denominator
condition allows cross-multiplication on `a < s.re`. In particular, the two
holomorphic functions agree in a neighborhood of the real point
`max a 0 + 1`, which lies in the positive half-plane. Mathlib's analytic
identity theorem extends their equality throughout that half-plane.
If the denominator vanished at a spectral point there, the identity would
force the numerator to vanish as well. Evaluating the Bezout identity from
`RatFunc.isCoprime_num_denom` then gives the contradiction `0 = 1`.
This proves the first conjunct.

For a complex point `z` with `0 < ‖z‖ < 1`, the proof explicitly chooses
`s = -Complex.log z / Real.log q`, with the real denominator embedded in
`ℂ`. Since `Real.log q > 0` and `Real.log ‖z‖ < 0`, the real part of `s`
is positive. The complex-power formula and `Complex.exp_log` show that
`spectralPoint q s = z`. The first conjunct therefore gives
`RationalEvaluation.RegularAt R z`, proving the second conjunct.
This uses only a logarithm at each individual nonzero point.

The imported statement and definitions are unchanged. Holomorphy remains an
explicit hypothesis. The proof asserts no regularity at zero or on the unit
circle, and no convergence or rationality existence for integrals.
