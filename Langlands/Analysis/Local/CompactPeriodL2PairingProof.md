# Proof of the modular compact-domain L² pairing

This module proves the unchanged published proposition
`Langlands.QuotientIntegration.CompactPeriodL2PairingStatement` as
`Langlands.QuotientIntegration.compactPeriodL2Pairing`.

The theorem retains independent group and parameter universes and all
published hypotheses on the actual measures, subgroup, parameter domain,
continuous maps and compact test. It imports the published compact-test
and quotient L² unfolding proofs without modifying them.

The proof constructs the actual compact auxiliary test `k` using the
weighted relatively compact domain theorem. Generic quotient L²
unfolding supplies the actual quotient vector and continuous test form
for its orbital average. Their almost-everywhere equality is rewritten
using the defining integral of `k`.

## Absolute product integration

A second auxiliary compact test integrates the product of the norms of
the weight and original test function. Its value is real and nonnegative,
so its complex norm equals that real integral. Generic quotient L²
unfolding, applied to this compact test and the specified measurable
L² representative, proves integrability of its norm times the norm of
the quotient representative on the ambient group.

Every fiber in the compact parameter domain is integrable because its
integrand is continuous on the compact domain closure. The integral of
the norm of the joint integrand is exactly the preceding majorant.
The product integrability criterion therefore proves absolute convergence
before Bochner Fubini is used. Fubini gives the uncorrected iterated
period identity and integrability of its outer function. Complex
conjugation commutes with the compact-domain integral; the scalar weight
factors out of the ambient integral.

## Actual right-Haar substitution

The ambient right measure is the inverse of an actual left Haar measure.
Pushing it forward by left multiplication by `a` is the inverse of the
right pushforward of the left Haar measure by `a⁻¹`. The existing actual
modular-character formula identifies that measure as `Delta(a⁻¹)` times
the right measure. The proof uses map composition and scalar pushforward;
it does not assume an inversion-density identity.

Consequently substitution by left multiplication by `a⁻¹` contributes
`Delta(a)` to integration against the right measure. Applied to the
specified strongly measurable quotient function, this gives

\[
 \int_G\overline{f(a^{-1}g)}\psi(\Gamma g)\,d\mu^{-1}(g)
 =\Delta(a)\int_G\overline{f(g)}\psi(\Gamma ag)\,d\mu^{-1}(g).
\]

This substitution identity holds for total Bochner integrals. Applying it
pointwise to the already justified Fubini formula transfers integrability
of the outer function to the modular-corrected outer function and gives
the exact target pairing. The proof keeps conjugation on the weight
because the Hilbert pairing is linear in its second argument.

The result proves neither a character specialization nor an actual
compact quotient period normalization. Relatively compact measurable
fundamental-domain selection, smoothness, integrated-action comparison,
period test separation, all-parabolic cusp identification and cuspidal
closedness remain separate obligations.

This is an internal analytic derivation of the published target, using
its public compact-test and quotient-unfolding results and pinned
Mathlib measure pushforward, Bochner Fubini and modular-character APIs.
Worker 116 authored the complete Lean proof and original explanation
in parent draft revision 39. Worker 1678 adopted the Lean unchanged,
updated this explanation and prepared the focused proof submission.
