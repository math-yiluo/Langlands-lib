# Functoriality of the actual all-test transporter relation

This internal module works with the existing `IsTransporter` relation. For
two homomorphisms `i₁, i₂` and a specified test-scheme point `g`, that relation
requires `i₁(h) g = g i₂(h)` after every refinement of the test scheme.

Restricting the point to another test scheme or precomposing both
homomorphisms preserves the relation. A homomorphism of ambient groups
carries a transporter point to one for the composite homomorphisms.
When that ambient map is monomorphic, it also reflects the relation. The
last property permits reflection of transporter equations through the
actual identity-component inclusion.

Arbitrary scheme base change preserves the relation with an explicit
recovery condition: under the actual pullback-point equivalence, the new
point must equal a specified refinement of the original point. Every
equation in the changed base is then obtained from an original-base
equation by that same point equivalence. There is no affineness, flatness,
smoothness or reducedness hypothesis in this comparison.
`baseChangeTransporterPoint` constructs this actual new point by the inverse
pullback-point equivalence. Its recovery equation holds exactly, and
`IsTransporter.baseChange_point` proves that it satisfies the required
all-refinement transporter relation.

Finally, an actual normalizing point with a specified torus automorphism is
an all-test transporter with the orientation used by the rank-one
reductivity criterion. The equality expressing the restriction of inner
conjugation is evaluated on every test point and rearranged by the group
law. The transporter is the same specified normalizing point.

The provenance is internal: the proofs unfold the actual transporter
equation, apply the group laws, use the existing pullback-point
equivalences, and evaluate the existing actual normalizing-point
definition. No normalizing point is constructed here, and no reductivity
or openness theorem is claimed.
