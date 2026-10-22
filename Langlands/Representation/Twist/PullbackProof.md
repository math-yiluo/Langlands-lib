# Proof of pullback compatibility

After extensionality at a group element `g : H` and vector `v : V`, both
actions reduce definitionally to `(chi (phi g) : R) • rho (phi g) v`.
`twist_comp` proves this equality, and `twistPullbackCompatibility` closes
the entire proposition target by introducing `chi`, `rho`, and `phi` and
applying `twist_comp`. Extensionality first compares the representations
as homomorphisms and then compares their values as linear endomorphisms;
the resulting equality is closed by `rfl`.

The four universe parameters `uR`, `uG`, `uH`, and `uV` remain independent.
The hypotheses are exactly a commutative ring `R`, groups `G` and `H`,
an additive commutative group `V` with an `R`-module structure, a unit-valued
homomorphism `chi : G →* Rˣ`, a representation `rho`, and a homomorphism
`phi : H →* G`. No topology, continuity, injectivity, smoothness, or finite
dimensionality is used. The closing theorem imports the accepted proposition
rather than restating or weakening it.

This is an internal proof from the definitions. The target is accepted statement
`68b9e381-f850-446e-9fa9-4dd178f19481` version 1, declaration
`Langlands.TwistPullbackCompatibility`, published at commit
`92099d5e2e1df96e2d39bb2ba898c43a28f02af8`. Its checked target fingerprint is
`a766cf17e0ba366a21cee235081561f8873b4a858ef7ade58cc82d1a5c7cf3b9`.
The imported twist definition is accepted artifact
`c83db975-8b79-4fbb-9901-2db836910a0a` version 1, published at
`3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1
(Lean 4.34.0; Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).

Worker 4 authored the Lean proof and initial explanation. Worker 9 adopted
the unchanged Lean draft, checked the published dependency hashes, and
expanded this explanation for submission. The original native compilation
and axiom inspection found only `propext` and `Quot.sound`; neither is proof acceptance.
Independent checking, semantic review, and publication remain required.
