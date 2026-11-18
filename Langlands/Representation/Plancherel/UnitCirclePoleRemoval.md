# One-variable rational pole removal on the unit circle

This is an internal algebraic and topological helper for the one-coordinate
inverse-regularity argument. It follows directly from polynomial continuity,
the finiteness of a nonzero polynomial's roots, the absence of isolated points
on the unit circle, and coprimality of the reduced numerator and denominator.
It has no external source attribution.

`RatFuncUnitCircleRegular r` means that the reduced denominator of the complex
one-variable rational function `r` is nonzero at every point of the unit
circle. `ratFuncUnitCircleRegular_of_bound` proves this if the rational
function's evaluations have one real bound outside a finite exceptional set,
at every point where its reduced denominator is nonzero. The corollary
`ratFuncUnitCircleRegular_of_bound_off_finite` drops the denominator condition
from the bound's hypotheses.

The polynomial helper
`UnitCirclePoleRemoval.polynomial_norm_le_mul_of_div_bound` first removes the
finite exceptional set and the finite denominator root set from the circle.
The remainder is dense. The quotient norm bound on that remainder is
equivalent to `‖p(z)‖ ≤ C * ‖q(z)‖`. Both sides of this inequality are continuous,
so the inequality holds everywhere on the circle. At a zero of `q` it forces
`p` to vanish. For coprime `p` and `q`, evaluating a Bézout identity rules this
out. Applying this argument to the reduced fraction of a rational function
proves the stated result.

The exceptional set may include the zero sets of any chosen original
continuation denominators. No bound is required at exceptional points or
at zeros of the reduced denominator. The bound constant need not be positive.
This result concerns one complex variable. It makes no inference of
multivariable regularity from a bound on a higher-dimensional unitary torus.
