# Global adjoint sections for fppf-locally inner automorphisms

Worker 561.

This is an internal descent construction for the natural pinned-comparison
problem. It uses the published fppf effective-epimorphism machinery and
`AutomorphicAction.isFaithful_of_isFppfQuotient_center`. It does not assert an
existence theorem for pinned corrections.

`AutomorphicAction.RepresentsIso a σ x` means that the action of the relative
point `x` agrees with the actual automorphism `σ` after every refinement of its
test scheme. For base sections this is equivalent to `a.basePointIso x = σ`.
Representatives of a faithful action are unique. Along a flat, surjective,
locally finitely presented cover they therefore satisfy the relation of the
cover, descend by `EffectiveEpi.desc`, and still represent `σ`. This gives a
unique base section when the covered test is the base.

`IsFppfLocallyInner σ` means that on one supplied fppf cover of the base the
automorphism is conjugation by a point of the original group, on every further
refinement. This definition makes no affineness, connectedness, nonemptiness,
quasi-compactness or reductivity assumption.

`IsFppfLocallyInner.existsUnique_adjointPoint` proves that such an automorphism
is the action of a unique global section of every supplied fppf quotient by the
full all-test centre, for every supplied action restricting to conjugation.
The proof maps the local conjugating point into the quotient and descends that
image by faithfulness. It requires no global lift to the original group.

Conversely, `IsFppfLocallyInner.of_adjointPoint` pulls an adjoint section back
along the supplied fppf quotient. On this canonical cover the section lifts to
the original group, and the supplied action becomes conjugation.
`isFppfLocallyInner_iff_existsUnique_adjointPoint` combines the two directions:
local innerness is equivalent to the existence of a unique representing
section in each specified full-centre quotient with its specified action.

The descent argument adapts the implemented all-refinement construction in
`LocalGroupIso.fppfDescendedRepresentative` to a single actual automorphism.
The conclusion is a prerequisite for the inner clause of
`RelativePinnedComparison`; no local pinning-normalization assertion is proved
in this module.
