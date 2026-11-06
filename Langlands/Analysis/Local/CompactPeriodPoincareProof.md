# Proof of compact-domain Poincaré periodization

This module proves the published proposition
`Langlands.QuotientIntegration.CompactPeriodPoincareStatement` as
`Langlands.QuotientIntegration.compactPeriodPoincare`.

A compactly supported continuous cutoff on the parameter space equals
one on the closure of the integration domain. Multiplying the original
weight by this cutoff gives a compactly supported continuous weight
with the same restricted-domain integrals.
The parameter measure restricted to the domain is finite because its
compact closure has finite measure.

For each ambient group element, the resulting joint integrand on the
subgroup times the parameter space is continuous and compactly
supported. Its subgroup coordinate lies in the preimage, under the
closed subgroup embedding, of the product of the compact parameter
image, the original test support, and the singleton of the inverse
group element. Its parameter coordinate lies in the compact weight
support. This proves joint integrability for the actual product measure.
More precisely, for a fixed ambient element `g`, the subgroup support is
contained in
`Subtype.val ⁻¹' (((j '' tsupport W) * tsupport f) * {g⁻¹})`,
where `W` is the cutoff weight. The ordered product follows directly
from the nonvanishing condition
`f ((j x)⁻¹ * (γ.val * g)) ≠ 0`. The closed subgroup embedding makes
this preimage compact, and the product measure is finite on compact
sets.

The cutoff equals one almost everywhere for the restricted measure.
The product projection transfers that equality to the joint measure,
proving absolute convergence for the original untruncated weight.
Bochner Fubini interchanges the subgroup and compact-domain integrals,
and the constant complex weight factors out of the subgroup integral.
Quotient induction identifies this identity with the existing orbital
averages.

The proof retains every target hypothesis and the independent universes
`uG` and `uX`. Fundamental domains, quotient period normalization,
smoothness, modular-corrected L² pairing, period test separation and
cuspidal closedness remain separate results.

This is a derived analytic proof of the existing target, using the
published quotient averaging API and pinned Mathlib's continuous cutoff,
compact-support integrability and Bochner Fubini theorems. Worker 116
authored the Lean proof in parent draft 37. Worker 1668 adopted the
unchanged Lean proof, expanded this explanation and prepared the focused
exact-target submission.
