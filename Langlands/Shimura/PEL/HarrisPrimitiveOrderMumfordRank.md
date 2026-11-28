# Ranks and twisted Euler polynomials for the fixed Harris order

Fix the Harris arithmetic and signature data and the named tensor, duality,
Weil transition, adelic comparison and finite étale torsion hypotheses.
Consider two positive-auxiliary polarized Harris objects over connected
locally noetherian quasi-separated bases on which every positive integer
is a unit. Each object carries a normalized frame at a point valued in
an algebraically closed field of characteristic zero and an actual
integral restriction of its rational order action. Let `mu` and `mu'` be
primitive representatives of their respective polarization rays.

For a common natural multiplier `k` and order element `a`, assume
the actual integral Rosati equations for `k • mu` and `k • mu'`.
`harrisPrimitiveMumfordTwist_nativeRank_eq` compares the ranks over
the chosen geometric fibres of the two twisted maps at each natural
parameter `j` for which both maps are isogenies. By
`IntegralRosatiEquations.mumfordTwist_eq`, each map is the action of
`harrisMumfordTwistOrderElement`, namely `j + tau(a) * a`, followed by the
corresponding multiple of the primitive
homomorphism. Here `tau` is the positive auxiliary involution on the order.
`harrisIntegralFrameFull_order` identifies both endomorphisms with the
same source operator. `primitivePolarizationComp_nativeRank_eq` then
gives equality of the native ranks.

`harrisPrimitiveOrderEulerPolynomial_eq` applies this argument over two
algebraically closed characteristic-zero fields, with the frames at the
identity points and with the same relative dimension. Take explicit
`AmpleMumfordPresentation` data for both multiples of the primitive
homomorphisms. Write `L` for the corresponding actual ample line bundle on
each side. `Rosati.mumfordEulerDegree` identifies the squares of the Euler
characteristics of the actual bundles `(i a)^* L ⊗ L^j` with the ranks
from the first comparison for all sufficiently large `j`.
`coherentEulerPolynomial_eq_of_eventually_sq_eq` then gives equality
of the actual twisted Euler polynomials.

`harrisOrderGraphBundle` is the exterior tensor product of `L` with
itself restricted to the graph, identified with the abelian variety by
the first projection. `harrisOrderGraphEulerPolynomial` is the Euler
polynomial of its actual powers. For each positive integer `r`,
evaluation of the twisted polynomial for `L^r` at `1` gives the
Euler characteristic of the `r`-th power of `harrisOrderGraphBundle`.
Pullback of tensor powers and distributivity over the tensor product
identify the line bundles. Using the twisted comparison for each
`r`, `harrisPrimitiveOrderGraphEulerPolynomial_eq` compares the graph
polynomials when the corresponding powers have the indicated ample
Mumford presentations.

`harrisPrimitiveCubicGraphEulerPolynomial` uses the canonical cubic
bundle of the ordinary datum with polarization `4 • mu`.
`Datum.cubicPowerBundleMumford` supplies the ample presentation with
Mumford map `(24 * r) • mu`. Scaling the Rosati equations and applying
the graph polynomial comparison proves
`harrisPrimitiveCubicGraphEulerPolynomial_eq` for that actual bundle.
`HarrisPrimitiveCubicGraphPolynomialUniform` collects the polynomials for
all order elements in a fixed relative dimension. The existence proof
uses the polynomials of one normalized field object if the zero family
fails to satisfy the condition. The comparison is independent of the
choice of full-level modulus.

`harrisOrderGraphBundle_isAmple_of_division` proves ampleness when
the order element is nonzero and the source algebra is division.
Its rational inverse clears to an actual endomorphism whose composite
with the order action is positive multiplication. The actual composite
is finite, which gives finiteness of the order action. Pullback along
that finite map and tensoring preserve ampleness.
`harrisOrderGraphEulerPolynomial_eval_finrank` identifies the polynomial
at each positive exponent with the dimension of global sections of the
corresponding ample power by higher cohomology vanishing.
`harrisPrimitiveCubicGraphEulerPolynomial_eval_finrank` applies this
calculation to the cubic bundle of `harrisQuadrupledFieldDatum`.
