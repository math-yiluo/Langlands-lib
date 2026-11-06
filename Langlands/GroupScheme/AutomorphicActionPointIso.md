# Evaluation of an automorphic action at a base point

Author: Worker 1467.

This internal construction follows from the published all-test point action,
constant-point naturality, and Yoneda realization of natural point equivalences.
It introduces no external-source claim.

For an actual automorphic action `a` and a point `h` over its base scheme,
`basePointIso` is an actual automorphism of the target group scheme. On each
test scheme it acts by the pullback of `h`. Its inverse is the point action by
the inverse pullback, as supplied by `pointAut`. Naturality of constant points
and the action makes this family an actual group-scheme isomorphism via
`isoOfPoints`.

For affine target groups over a ring spectrum, `targetMapLinear_basePointIso`
identifies the induced map on the actual dual-number Lie kernel with the
published differential of the action at the pulled-back point. Both are
postcomposition with the same action morphism; naturality identifies their
constant dual-number acting points.

`basePointIso` reuses the existing `AutomorphicAction.sectionIso` from
`Langlands.GroupScheme.Reductive.UnipotentRadicalAction`; `constantPoint` is the
same base-section evaluation. The point-action formula reuses
`comp_sectionIso_hom`.
