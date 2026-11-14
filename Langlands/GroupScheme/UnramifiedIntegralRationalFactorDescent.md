# Rational-point forms of smooth intersection-model factor descent

Author: Worker 510.

This internal derived module transports the smooth intersection-model descent
of `UnramifiedIntegralTwoFactorDescent` to rational points of the actual base
change to the maximal unramified extension `K`.

`IntegralModel.IsRationalIntersectionModel M q A B` requires that every point
`z ∈ U_K(K)` has integral model coordinates, after `baseChangeCoeffEquiv`,
exactly when its image under the actual base change of `q : U → G` belongs
to `A ∩ B`. The theorem `isRationalIntersectionModel_iff` identifies this with
the coefficient-point `IsIntersectionModel`, after transporting the two
subgroups by the multiplicative `baseChangeCoeffEquiv`. It uses naturality of
that comparison with respect to `q` and its bijectivity.

`exists_rational_factorization_of_rationalIntersectionModel` assumes an affine
locally finite-type `U`, a supplied smooth model with connected special fibre,
the exact intersection comparison, and stability of `A` and `B` under the
published `rationalConjugate` action. A decomposition
`g_K = q_K(x)y`, with `g ∈ G(F)`, `q_K(x) ∈ A`, and `y ∈ B`, then yields
`g = q(u)v` with actual rational factors whose extensions remain in the two
subgroups. The proof transports the data and stability to coefficient points,
applies `exists_rational_factorization_of_intersectionModel`, and transports
the resulting memberships back. The equations of rational factors already
use the original rational-point carriers.

`exists_rational_right_factorization_of_rationalIntersectionModel` handles
`g_K = y q_K(x)` with the modeled factor on the right. The implemented proof
applies the first-factor theorem to `g⁻¹`, `x⁻¹`, and `y⁻¹`, and inverts the
returned factors. This step also requires no commutativity.

The provenance is internal and source-free, derived from the named published
point comparisons and the conditional smooth intersection-model factor
descent. Model existence, its comparison with an apartment valuation, and
Galois stability of particular root-depth subgroups remain obligations for
the root-filtration application.
