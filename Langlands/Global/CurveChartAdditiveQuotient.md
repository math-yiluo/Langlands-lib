# Additive quotient of the normalized parameter charts

For a field extension \(F/k\) and a parameter \(s\in F\), write
\(B\), \(C\) and \(D\) for the normalized chart algebras of \(s\),
\(s^{-1}\) and \((s,s^{-1})\), respectively. These are the existing
`CurveModel.chartRing` subalgebras of \(F\). The subspace
`curveChartSum` is \(B+C\) inside \(F\). The subspace
`curveChartAdditiveQuotient` is the image of \(D\) in \(F/(B+C)\).
Equivalently it is the additive quotient of the actual overlap by
sums of functions on the two charts.

`finite_curveChartAdditiveQuotient` proves this quotient finite when
\(k\) is finite, \(s\ne 0\), and \(F\) is finite over \(k(s)\).
`FiniteConstantCurveChart.moduleFinite` gives a finite free basis of
\(B\) over the principal ideal domain \(k[s]\), using torsion freeness.
Every function on \(D\) has a numerator in \(B\) after multiplying by
a power of \(s\), by `CurveModel.exists_pow_mul_mem_chartRing`. For
each element of the basis a sufficiently large power of \(s^{-1}\)
places it in \(C\), by the same denominator lemma on the second
chart. Consequently the only monomials needed to span the additive
quotient are a finite list of inverse powers of \(s\) times the
chosen basis elements. A finitely generated module over the finite
field \(k\) is finite.
