# Actual families for equal-rank gamma continuation

This internal module constructs right translates of inverse-character
Whittaker functions. A translate of a coefficient realized by a functional
and vector is realized by the same functional and the translated vector.
Translation by the fixed central matrix `(-I)^n` multiplies every coefficient
in a model with minus-one scalar `ζ` by `ζ^n`. The actual equal-rank integral
has the same scalar identity. This identity uses the total Bochner integral
and does not assert convergence.

For `1 < q` and a reflection unit with value `q⁻¹`, the reflected rational
form of the gamma equation proves that its scalar `ζ^n` can be absorbed into
the primal rational continuation, giving a gamma equation with scalar one.
This is a pointwise statement for a supplied model scalar; it does not
assert that the scalar stays constant in a family.

For an inverse-character family with a common compact open right level and
pointwise entire parameter dependence, a fixed right translation conjugates
the common level. The actual second-dual transform instead pulls the level
back under inverse transpose. Both transformed families retain pointwise
entire dependence. Given a fixed full Whittaker-type first representation,
a model coefficient, two Schwartz tests, and a quotient measure finite on
compact sets, the equal-rank slice theorem therefore proves that both
literal slice families are entire. The primal family uses the fixed central
translate and the dual family uses the unshifted second-dual transform.
No Fourier relation between the two tests is needed for this entireness
assertion.

The proofs adapt the elementary level-transport arguments already used in
`AdjacentRankDualEntireCoefficientFamily`, and compose the published
equal-rank slice and rational gamma identities. This module supplies actual
analytic families; real-ray clearing, rational continuation and gamma
equations, and both closed dominant-rank targets remain further obligations.
