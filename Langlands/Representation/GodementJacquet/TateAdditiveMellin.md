# Exact additive and multiplicative Tate integrals

Worker 357 derives an exact comparison between the existing additive-Haar
abelian Tate zeta integral and the multiplicative-Haar scalar Mellin integral.
The field has its canonical p-adic topological data, the prime and field
universe are arbitrary, and the additive Haar measure is supplied without a
self-duality condition. The quasicharacter is continuous and the scalar test
is locally constant with compact support.

`TateAdditiveMellinStatement F` asserts positivity of the additive measure of
the integral units, equivalence of genuine integrability for the two
integrands, and equality of the Mellin integral with the additive zeta
integral divided by that same positive unit mass. The included theorem
proves the proposition for every character, test and complex parameter.
The equality uses the original Bochner integral definitions, including
their totalization when integrability fails; the separate equivalence
retains the convergence obligation.

The proof reuses the published determinant-density cancellation for GL₁
and its scalar-coordinate comparison. The actual scalar isomorphism from
field units to GL₁ preserves the existing multiplicative Haar measures.
Evaluating the determinant and unique matrix entry therefore turns the
natural determinant weight into the normalized absolute value of the scalar.

The proof identifies the existing positive Haar-comparison scalar exactly.
The indicator of the integral units has multiplicative integral one.
Its natural determinant weight equals one on its support, so the same
density-cancellation formula gives one as the inverse comparison scalar
times its additive mass. Cancelling the positive scalar identifies it with
that mass, proving positivity as well. No normalization is chosen or assumed.

At a nonzero scalar the additive integrand contains
`exp((s - 1) log |x|)`. Multiplication by the natural weight `|x|` gives
the original Mellin factor `|x|^s`, with the principal complex power and
positive real absolute value fixing the logarithm. The quasicharacter
extended by zero agrees with the original character on field units.
The published scalar density theorem and measure-preserving scalar
isomorphism now give both the integrability equivalence and the integral
identity with the computed factor.

This is an internal derivation from published actual measure comparisons
and the existing callable integrands. It introduces no alternative zeta
integral or factor definition. Its purpose is the analytic bridge between
the scalar JPSS model integrals and the concrete abelian Tate functional
equation. Identification of their epsilon coefficients and exponents,
arithmetic compatibility and the closed correspondence remain separate
obligations.
