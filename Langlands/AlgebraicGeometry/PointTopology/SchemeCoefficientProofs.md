# Coefficient continuity and openness for actual scheme points

Proof author: Worker 105. Verification and submission: Worker 1329.

The theorem `schemeCoefficientProperties_proof` proves
`Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProperties R S T` on the actual relative
scheme-point carriers with exactly the chart-final topologies and hypotheses
of `SchemeCoefficientStatements`. The base and value rings lie in an arbitrary
common universe, and the base ring R has no topology.

The naturality identity `changeRing_openPointMap` is associativity of actual
relative scheme morphisms: precomposition with Spec(f) commutes with
postcomposition by an open-subscheme inclusion.

For continuity, an open set pulls back to an open set in every affine source
chart. The naturality identity expresses this pullback through the affine
coefficient map and then the same target chart inclusion. The existing affine
coefficient continuity theorem and the defining continuity of a final-topology
chart prove openness of this pullback. The defining final topology then gives
global continuity. This part uses no local-ring or ring-topology properties.

For openness, local S ensures that every S-point factors through an affine
open chart. Given a point p of an open set W, select such a chart and lift q.
The chartwise inverse image of W is open by the definition of the final
topology. The chart is locally of finite type because its structure map is
the composite of an open immersion with the structure map of X. The existing
affine coefficient theorem therefore gives an open image under f on this
chart. The target chart map is open, using local T, continuous multiplication
and `IsOpenUnits T`. Its image is an open neighborhood of the image of p
contained in the image of W, by the naturality identity. Thus the whole image
of W is open. No source unit condition, quasi-compactness or separatedness is
used, and the proof asserts no global injectivity.

The source motivation and the precise generalization of the local argument in
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), Theorem 3.6
proof, printed page 8, are explained in the target's paired Markdown. This
proof is only the coefficient-map step; DVR and adelic specializations and
separated-point injectivity remain separate.

Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
