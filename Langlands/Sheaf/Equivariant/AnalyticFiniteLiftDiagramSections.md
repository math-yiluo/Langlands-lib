# Fixed sections on common equivariant analytic lift diagrams

This internal construction combines `AnalyticFiniteLiftDiagrams` with
`AnalyticFiniteFixedSections`. It prepares the fixed sections needed to map free
equivariant representables to a restricted coefficient presheaf in the compact
quasi-étale comparison argument. Its mathematical inputs are the already defined
common equivariant diagram and the finite simultaneous fixed-section lemma.

Let a finite family of compact quasi-étale objects over an analytic space have
supplied continuous local action lifts. Let a finite family of ordinary arrows
connect these objects, and let `Q` be a prescribed open subgroup of the acting
group. The coefficient `F` is a presheaf in a concrete category, discrete for the
actual compact analytic lift system. A section of `F` is supplied at each vertex.

`CommonEquivariantFixedLiftDiagram` records a common equivariant lift diagram
below `Q`, together with fixedness of all supplied sections for the original
analytic lift actions on that subgroup. Given an existing common diagram,
`CommonEquivariantLiftDiagram.fixSections` applies `finiteLiftFixedSections` with
the diagram subgroup as its upper bound, then shrinks the diagram to the
resulting subgroup. Shrinking preserves the equivariance of every supplied
arrow. The construction needs only finitely many vertices; its edge family may
be arbitrary because its initial diagram is supplied.

`commonEquivariantFixedLiftDiagram` additionally constructs that initial
diagram when the edge family is finite, under the explicit hypothesis
`HasCompatibleCompactQuasiEtaleLifts`. Thus it gives a common subgroup for both
arrow equivariance and simultaneous fixedness. It does not prove this
compatibility hypothesis, construct missing analytic lifts, or construct
geometric tuple cones.

For every vertex, `subgroupInclusion_map_globalLift_action` identifies the
normalized global action with the supplied analytic lift action after applying
the actual subgroup-inclusion functor on twisted sites. The proof uses
`TwistedOver.hom_ext`: both the twist and the underlying analytic arrow agree
definitionally, including the inverse twist convention.

`globalFixedSection` then places the supplied section in
`GlobalLift.FixedSections` for the normalized vertex lift and the actual
subgroup-restricted coefficient `((subgroupInclusion ρ H).op ⋙ F) ⋙ forget A`.
The action identity reduces its fixedness condition to the recorded original
fixedness. `globalFixedSection_val` states that its underlying section is exactly
the supplied one. No sheaf, injectivity, free-representable discreteness, or
cohomological vanishing assertion is made by this module.
