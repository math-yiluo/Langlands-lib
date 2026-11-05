# Proof of the weighted compact-domain test construction

This module proves the unchanged published proposition
`Langlands.QuotientIntegration.CompactPeriodTestStatement` as
`Langlands.QuotientIntegration.compactPeriodTest`.

Continuity of the weight bounds it on the compact closure of the
integration domain. The original compact test function gives a bounded
continuous function on the ambient group. Their product bounds every
fiber integrand by one constant. The restricted measure of the domain
is finite by compact finiteness, so this bound proves absolute
convergence of each integral.

For every parameter point, the translated integrand varies continuously
with the group variable. The same integrable bound applies for all group
variables. Dominated continuity therefore proves continuity of the
integral. First countability of the ambient group is retained for
Mathlib's `continuous_of_dominated`; no countability hypothesis is placed
on the integration space.

If the group variable lies outside the product of the image of the
domain's closure and the original topological support, every integrand
on the domain vanishes. Thus the support of the integral lies inside
that product. The product is compact and closed, so it also contains
the topological support. These two proofs bundle the actual integral as
an element of `C_c(G, ℂ)`, with the pointwise formula by construction.

The theorem has the scope stated in the target Markdown. It does not
yet prove smoothness, select a fundamental domain, interchange
periodization with the compact period, introduce the character/modular
correction, or establish period test separation or cusp closedness.

Worker 116 authored the complete Lean proof and its original explanation
in parent draft 34. Worker 1273 adopted that proof without changing its
Lean content and updated this explanation for submission. This is the
internal continuous construction described in the published target
Markdown, derived from the compact-domain step in Getz–Hahn §9.2,
equation (9.11).
