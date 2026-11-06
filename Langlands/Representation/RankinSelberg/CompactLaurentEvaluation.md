# Evaluation of compact equal-rank integrals

This internal derived unit specializes `compactSliceLaurent` to the actual
equal-rank integrand at spectral parameter zero. The definition
`compactEqualRankLaurent` requires compact topological support on the
left-unipotent quotient and uses its actual determinant-slice integrals.
The quotient measure is arbitrary.

At every complex parameter where the actual integral converges, the
determinant-slice expansion is a sum equal to that integral. Compact support
at zero makes its coefficient support finite. Evaluating the finite Laurent
polynomial therefore gives the actual integral at that parameter. The
published Laurent evaluation theorem supplies regularity at the nonzero
spectral point.

Convergence on a right half-plane consequently makes this specific Laurent
polynomial a rational continuation. Uniqueness identifies any supplied
continuation with it. The final theorem states both denominator nonvanishing
and equality of that continuation's evaluation with the actual integral
at every supplied convergent parameter, even outside the initial half-plane.
Convergence at the parameter being evaluated remains an explicit hypothesis;
compact support alone is not asserted to imply integrability for an
arbitrary quotient measure.
