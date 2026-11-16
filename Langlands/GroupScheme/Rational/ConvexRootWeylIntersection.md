# Weyl intersection for individually convex root subsets

This internal consequence concerns the actual relative Weyl group of a
maximal split torus `i` in a connected reductive group over an arbitrary field.
Let `S` and `X` each be convex subsets of the full set `relativeRoots i`, in
the published cone sense. Their symmetric parts are `parabolicRootLevi S`
and `parabolicRootLevi X`. The intersection of the reflection-generated
Weyl subgroups of these parts is the reflection-generated Weyl subgroup of
`parabolicRootLevi (S ∩ X)`.

`ConvexRootWeylIntersectionStatement` packages this formula uniformly, and
`convexRootWeylIntersection` proves it. The statement permits nonreduced
relative root systems and rank zero. Both individual convexity assumptions
are retained.

The proof applies character-displacement containment to an element in both
Weyl subgroups. For every actual character, its rationalized displacement
lies in the intersection of the rational spans of the two symmetric parts.
The rational-subspace stabilizer theorem expresses that Weyl element using
root reflections in ambient roots rationalizing into this intersection.
Convex symmetric-span saturation, applied separately to `S` and `X`,
identifies these ambient roots with their common symmetric roots. The
relative root system supplies stability of the ambient root set under
negation. The symmetric part commutes with intersection, giving the
claimed inclusion. The reverse inclusion follows by monotonicity of the
reflection-generated subgroup under inclusion of its generating roots.
The two elementary helper lemmas establish this commutation and monotonicity.

The provenance is an internal derivation from character-displacement
containment, rational-subspace Weyl stabilizers and convex symmetric-span
saturation. It does not require equality between the rational span of an
intersection and the intersection of rational spans. This module proves
only the Weyl-group formula; the group-scheme intersection statement is a
separate result.
