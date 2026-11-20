# Pointwise nonvanishing of ordinary normalized p-adic tests

`padicOrdinaryEqualZetaValues` and `padicOrdinaryUnequalZetaValues` use the
canonical measure on the quotient by the smaller upper unipotent group.
The unequal family uses the ordinary integral, with the rectangular variable
having zero rows. The equal family includes the Schwartz–Bruhat test factor.

The canonical quotient measure is compatible, so the p-adic L-polynomial
certificate gives a normalized generator for each respective family. For
a fixed complex argument `s₀` the normalized Laurent evaluation at `q^(-s₀)`
is nonzero on some rational value in the family. Membership provides the
actual two Whittaker functions and, in equal rank, the Schwartz–Bruhat
function. Evaluating its Laurent normalization at the spectral variable gives
an entire function that is nonzero at `s₀`. On a sufficiently far right
half-plane the integral is absolutely convergent and equals this
normalization times the reciprocal of the specified L-polynomial.

This applies J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
§3.1, Theorem 3.1 and the two paragraphs following it, p. 213 (PDF p. 216),
to the two local integral families used in the global argument in §4.2,
p. 222 (PDF p. 225). The registered source `cogdell-2004-analytic-theory-gln`
has SHA-256 `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The proof uses the published p-adic certificate and the evaluation lemmas
of `NormalizedZetaEvaluation`.
