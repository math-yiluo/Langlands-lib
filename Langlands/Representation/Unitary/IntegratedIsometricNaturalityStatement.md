# Naturality of the actual Bochner integrated action

Worker 116 states
`Langlands.Analysis.IntegratedIsometricNaturalityStatement`.
For a measurable group G, a complete complex normed space E, any measure μ,
a norm-preserving group homomorphism π into bounded complex-linear
endomorphisms, AE strongly measurable orbits and an integrable scalar
weight f, let T be the actual `integratedIsometricAction` constructor.
Group and space universes are independent. The formula is
T x = ∫ g, f(g) • π(g)x dμ(g).

For every actual closed complex submodule P invariant under every π(g),
the conclusion supplies an actual preservation proof hTP: T(P) ⊆ P.
For every actual complex-linear isometric equivalence U:P≃Q onto any
ambient complex submodule Q, if U intertwines the original group action
on P with that on its image in E, then U also intertwines T. The equation
is written in E:

U( T x viewed in P ) = T( U x viewed in E ).

The subtype on the left uses the supplied hTP. The existential witness is
a proof of preservation, not an assumed operator or an assumed
compatibility equation. There is no separate closedness or invariance
premise on Q and no assumed equality involving T in the hypotheses.
These quantifiers match the compatibility premise of the separate
compact-approximation multiplicity criterion. An application first derives
norm preservation from its unitary inner-product identity and establishes
the orbit measurability and scalar integrability premises.

This is an internal Bochner naturality extraction from Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), section 3.4,
printed pp.85–86, one-based PDF pp.101–102, and the integrated-operator
argument of Lemma 9.3.1, printed pp.246–247, one-based PDF pp.258–259.
The registered source is `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The first passage defines the weighted integrated action, with right Haar
measure and the same action convention. The second uses restriction to
closed invariant subrepresentations and transports a nonzero eigenvalue
to equivalent constituents to bound multiplicity. The present target
makes the underlying integral preservation and transport step explicit,
rather than substitute preservation alone for intertwiner compatibility.
It is stated for arbitrary measure and isometric Banach actions because
these properties suffice for this step. It does not assert a comparison
with a separately constructed Gelfand–Pettis integral.

The complete October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no correction to section 3.4 or Lemma 9.3.1. The original passages and
the complete errata were read directly.

The internal proof route is to integrate the weighted orbit inside P.
Closedness makes P complete. The subtype linear isometry commutes with
Bochner integration, so its integral embeds as T x and proves preservation.
Composing U with the subtype inclusion Q→E gives another linear isometry
from the same complete P into the complete ambient E. It commutes with
the same integral; complex linearity and group intertwining identify its
integrand with the weighted orbit of Ux. This needs no completeness
instance on Q. The pinned Mathlib theorem
`LinearIsometry.integral_comp_comm` applies to these two maps.

This file defines the proposition only. A separate exact published-target
child must prove it. No convolution law, Dirac sequence, symmetry,
compactness, strong approximation, decomposition, finite multiplicity,
automorphic quotient or concrete Hilbert realization is asserted here.
In particular, the abstract compact-approximation criteria still require
these remaining operator hypotheses in an actual application.
