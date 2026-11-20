# A right half-plane for complex Schwartz Godement tests

The rectangular Schwartz test in a Godement section restricts to a
Schwartz test on square matrices by `X ↦ X · trailingRows(g)`. The map has
a continuous linear left inverse obtained by multiplying on the right
by `g⁻¹` and retaining the trailing columns. This gives the required
norm bound for composition on Schwartz space.

`ComplexGodementSchwartzStatement` assumes a continuous smaller-group
input whose value at `h⁻¹` has norm at most
`C * complexMatrixHeight h ^ M`. Continuity gives a.e. strong measurability
of the integrand for the determinant-density Haar measure. The complex
character's angular factor has norm one, so the absolute integrand is
bounded by `C` times the height-weighted square Schwartz test with
determinant exponent `d.exponent + (m+1)/2`. Applying the square-matrix
Schwartz estimate gives absolute convergence when the real part of this
exponent is at least `m + M`. Jacquet's smooth standard input in (7.1)
satisfies the continuity hypothesis.

[Jacquet, *Archimedean Rankin–Selberg integrals*, Lemma 3.3 and §7.1, pp. 13 and 43–44](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
