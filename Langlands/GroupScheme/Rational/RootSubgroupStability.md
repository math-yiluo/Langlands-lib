# Stability of the intrinsic relative-root subgroup functor

This module proves elementary functorial laws of the intrinsic construction in
`Rational.RootSubgroup`. The base is any scheme B, S is any commutative group
scheme, i is any homomorphism from S to G, and a is any character. No field,
splitness, smoothness, or nonzero-character hypothesis is needed.

The imported `RootSubgroupStabilityProof` supplies `orbit_conjugation`,
`IsOrbitExtension.conjugate`, and `subgroup_isStable`. These identify the orbit
after a constant torus action, construct the corresponding affine-line
extension, and prove stability on every test scheme. The extension is named
`conjugateExtension`; unfolding it gives the constant action on the supplied
extension.

`AutomorphicAction.evalZero_act` gives the general action law: evaluating an
extension acted on by a constant point at zero is the action on its original
zero value. `subgroup_isNormalizedBy_range` uses the imported stability theorem
to prove normalization by the actual image of S.

For any supplied representative j of this intrinsic subgroup, `subgroupAction`
constructs its actual full-torus action using `onRepresentedSubgroup`.
`subgroupAction_act_comp` proves that the representing inclusion intertwines
this action with conjugation in G, on every test scheme. Representability is
an explicit input of this construction, not an assertion made by this module.

These are derived internal laws of the published character-orbit construction,
whose source context is documented in its own paired Markdown. The module proves no Lie-image
or representability statement and does not yet identify the generated cyclic
semigroup functor with the intrinsic subgroup.
