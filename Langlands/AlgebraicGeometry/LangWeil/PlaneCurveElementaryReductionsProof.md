# Elementary plane-curve reductions

Author: Worker 2969.

The theorem `planeCurveElementaryReductions` targets the exact unchanged
`PlaneCurveElementaryReductionsStatement`. Its source is the elementary
coordinate reduction on printed p.349 of Wolfgang M. Schmidt, *Zur Methode
von Stepanov*, Acta Arithmetica 24 (1973), registered source
`schmidt-1973-zur-methode-von-stepanov`, with the corrected linear-case error
bound already specified in the statement.

The first clause uses `planeCurve_separable_model`. When a partial
derivative vanishes, an optional coordinate exchange followed by
one-coordinate Frobenius contraction preserves absolute irreducibility and
the rational zero count while strictly decreasing the sum of the positive
partial degrees. Strong induction terminates with both derivatives
nonzero. A final coordinate exchange orders the degrees; their maximum and
minimum have not increased.

The second clause uses `planeCurve_linear_zero_count_error`. Write the
actual curve as `a(X)Y + b(X)`. The leading coefficient is nonzero, and
irreducibility excludes common field roots of its two coefficients. Above
each abscissa where `a` does not vanish there is exactly one rational
point, with second coordinate `-b/a`. The missing abscissae are roots of
`a`, whose degree is at most the first partial degree of the curve.

All auxiliary modules are implementation proofs. No norm-polynomial
existence or Hasse–Weil estimate is assumed. The four proof modules compile
in the pinned environment; the theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`. Compilation alone supplies no
independent mathematical acceptance.
