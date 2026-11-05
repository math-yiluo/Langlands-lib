# Scalar Iwasawa bounds for the actual standard quotient integral

This internal construction reduces scalar convergence of the existing
standard intertwining integral to integrability of an explicit scalar weight.
It uses the original source normalized induction and actual left quotient
`(U ∩ U') \ U'`. The group and representation-carrier universes are independent;
the carrier has no topology or norm.

The quotient integrand is locally constant: its pullback to `U'` is the
restriction of a right translate of the smooth source function. Local
constancy descends through the quotient topology. Composing with an actual
smooth-dual functional gives a continuous complex function and hence strong
measurability for every Borel quotient measure. No second countability
assumption on the group is used.

The full scalar domain equals the whole source if and only if every scalar
test of every source function is integrable at the identity. For a general
evaluation point, apply the identity case to the source's actual right
translate.

Let `K` be compact and open, and let a nonnegative function `ξ : M → ℝ`
bound every coefficient of the inducing representation up to a positive
constant depending on its vector and smooth functional. Restriction of a
source function to `K` is locally constant and has finite range. Choose the
maximum of coefficient constants on this finite range, enlarged to at least
one. Covariance then gives a common constant `C > 0` with

`‖ℓ(f(u'g))‖ ≤ C * ‖δ_U^(1/2)(m)‖ * ξ(m)`

for every actual factorization `u'g = p k`, where `m` is the Levi projection
of `p`. Here the half-character is the existing positive Haar half-character
on `M`, exactly as used by the source Levi-inflated normalization. This
estimate holds uniformly in the evaluation point and all factorizations;
it is distinct from the published compact product-induced coefficient bound.

`iwasawaWeight` is the product of this half-character's complex norm and
`ξ`, evaluated on supplied parabolic coordinates of actual quotient points.
The convergence criterion requires parabolic and compact coordinates such
that each quotient point has a representative with the stated factorization.
Integrability of the weight is an explicit hypothesis, not a property
silently attributed to a chosen section. Multiplying that integrable weight
by `C` and using the proved scalar measurability gives scalar integrability
by domination. Right translation supplies all evaluation points.

The provenance is internal: the proof combines the existing covariance,
quotient topology, compact finite-image lemma and scalar dominated
integrability. It proves no polynomial coefficient-growth theorem, no
geometric weight-integrability estimate and no rational continuation. Its
intermediate hypotheses remain obligations in an application to the
unchanged actual-point intertwining target. Original-carrier
representability can subsequently be obtained from
`scalarDomain_eq_domain` under its explicit admissibility and existing
Haar/modulus hypotheses.
