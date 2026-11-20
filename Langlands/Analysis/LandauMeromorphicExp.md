# Landau's theorem for a meromorphic continuation of the exponential

`Langlands.GeneralDirichlet.MeromorphicExpLandauStatement` concerns a
general Dirichlet series with nonnegative real coefficients and nonnegative
real exponents, indexed by an arbitrary type. Suppose the series converges
at a real point `σ₁`. Suppose its exponential agrees on `Re s > σ₁` with a
function meromorphic on `Re s > σ₀`, with nonnegative meromorphic order at
each real `σ > σ₀`. Then the series converges at every real `σ > σ₀`.

The proof uses `summableAt_of_abscissa` from `LandauDirichlet`. At a putative
abscissa `σc > σ₀`, the series is holomorphic on `Re s > σc`. The difference
between the continuation and the exponential of the series has order
infinity on the overlap with `Re s > σ₁`. The meromorphic identity theorem
propagates this equality of germs throughout `Re s > σc`. The normalized
meromorphic continuation therefore agrees pointwise there with the
exponential.

Nonnegative order at `σc` makes the normalized continuation analytic
there. Its real part is at least one on the real interval immediately to
the right, by nonnegativity of the series, and hence also at `σc` by
continuity. The principal complex logarithm of the normalized continuation
is analytic on a small disc centered at `σc`. It agrees with the series near
a real point on the right of the disc, since the series is real there and
its imaginary part stays in `(-π, π)` in a neighborhood. The analytic
identity theorem propagates equality over the intersection of the disc
and the half-plane. `summableAt_sub_of_taylor` now gives convergence to the
left of `σc`.

This is a derived version of Hardy and Riesz, *The General Theory of
Dirichlet's Series* (1915), Theorem 10, printed p. 10 (PDF p. 26 in
`hardy-riesz-1915-dirichlet-series`). Hardy and Riesz supply the Taylor
argument for the series itself. The extra steps here construct the
holomorphic extension passed to the existing Library implementation of
that argument.
