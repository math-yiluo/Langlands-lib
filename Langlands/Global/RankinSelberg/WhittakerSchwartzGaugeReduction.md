# Reduction of the weighted Whittaker–Schwartz estimate to simple-root gauges

This internal proof is conditional on pointwise simple-root majorization
and uniform convergence of the concrete diagonal majorants. It does not
prove either analytic input and does not claim an unconditional proof of
`WhittakerSchwartzGaugeStatement`.

The proof chooses the common central exponent β supplied by
`HasCentralPowerBound`, then applies
`WhittakerSimpleRootMajorizationStatement` to obtain one gauge exponent τ
uniform over all vectors and standard characters. The explicit torus
hypothesis supplies a nonnegative threshold C and one Haar measure on the
full idele torus, chosen before the determinant exponent and the two
Schwartz functions. Every diagonal majorant above C is finite. The
previous quotient-application theorem converts this hypothesis to
finiteness of the actual gauge integral, uniformly over the gauge and the
last-row Schwartz–Bruhat factor.

The resulting threshold is `max 0 (C - β)`, chosen before the character,
vector, Schwartz function and integration exponent. Given σ above that
threshold, σ + β exceeds C. Pointwise gauge majorization, multiplication
by the two nonnegative weights, and the identity
`|det g|^β |det g|^σ = |det g|^(σ+β)` bound the desired lower integral by
the finite gauge integral. Positivity of `detNorm` justifies the real
power identity. Monotonicity of the lower integral finishes the proof
without any additional measurability assumption on its left side.

The conclusion is exactly the existing proposition at universe u, with
its actual adelic quotient and existing measure. This is a derived Lean
composition of analytic inputs, rather than an argument attributed
verbatim to the literature. It imports no additional proposition asserting
the gauge integral: the diagonal finiteness premise and its application
are both explicit.
