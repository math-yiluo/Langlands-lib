# Real principal-series Whittaker uniqueness

`RealPrincipalSeriesWhittakerUniquenessStatement` concerns complex-linear forms
on the full smooth normalized real character principal series. It assumes a
finite compact right-derivative bound on each form and the same upper-unipotent
Whittaker covariance. If the first form is nonzero, the second is a complex
scalar multiple of it.

The reversal cell is a free open orbit for the product of the Borel and the
upper unipotent group acting by \((b,u)\cdot x=b x u^{-1}\). Its orbit
homeomorphism uses upper-unipotent and diagonal coordinates on the Borel,
with the diagonal reversed on crossing the long Weyl representative. The
action is continuous in the norm of the matrix-space operators.

Compose each form with Borel averaging and restrict to the tests of the cell.
Left multiplication on the tests contributes the inducing character and the
modular factor from left translation of right Haar measure. Inverse right
multiplication contributes the Whittaker character on the inverse unipotent.
Both test functionals therefore have the same continuous covariance on the
free open orbit.

If the first restriction vanished, Bruhat support descent would force its
ambient distribution to vanish. Surjectivity of Borel averaging and the real
and imaginary decomposition of complex tests would then force the original
form to vanish. The open-orbit proportionality theorem now gives a scalar.
The difference of the two ambient distributions after scaling vanishes on
the reversal cell and retains both unipotent covariance laws. Bruhat descent
makes this difference zero, and injectivity of the distribution construction
returns the proportionality of the inducing forms.

This is an internal comparison theorem for real Whittaker realizations in
the Rankin–Selberg proof.

`realPrincipalSeriesWhittakerOrbitFormula` also identifies the restriction of a single nonzero form composed with Borel averaging. On each complex test supported in the longest cell, its value is a fixed nonzero multiple of the left Haar integral on the Borel and upper-unipotent product. The integrand is the inverse inducing weight, the Borel modular character, the right Whittaker character and the test at `b w₀ u⁻¹`. The modular factor comes from the covariance of the right-Haar Borel average. The nonzero restriction proved by Bruhat descent lets the free-orbit formula identify the scalar.

This derived formula gives the character-principal-series comparison on the
full longest cell. The corresponding two-block calculation evaluates a
Casselman section by integrating over the upper-right matrix rectangle.
See the proof of Proposition 14.1, pp. 103–104 of the author-posted edition of
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=103).
The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
