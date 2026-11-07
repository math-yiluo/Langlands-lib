# Conditional reduction of the VI.4.5 block center to VI.4.1

Worker 1153. This internal adapter implements the categorical step in Renard
VI.4.5 (printed p.160 / PDF p.166), using the registered 9 July 2026 source
`renard-2026-representations-groupes-reductifs-padiques`. The source obtains
this isomorphism from VI.4.1 and the module example of A.X (printed p.269 /
PDF p.275). The exact statement pair remains unchanged.

For an object X of the actual rational inertia block, forgetting the proof of
block membership is a ring isomorphism from End X in the full subcategory to
End X.obj in smooth representations. Taking centers and composing with
`Langlands.Renard.generatorCenterEquiv` gives
`rationalInertiaBlockCenterEquiv`. Its forward map is exactly the component
of a natural endomorphism at X, followed by the full-subcategory morphism
projection. The subring center and the underlying ring of the complex
subalgebra center agree definitionally.

`rationalSummandBlockCenter_of_homEquivalence` takes the published
`RationalSummandHomEquivalenceStatement` as an explicit premise. Applied with
all the original hypotheses it supplies compact-induction membership and
an equivalence for the actual Hom functor. Its full and faithful instances
therefore give the required evaluation isomorphism. Every original universe,
local-field premise, reductivity and standard-parabolic premise, irreducible
cuspidal representation, and irreducible norm-kernel summand with injective
map is retained by the exact target.

This is a conditional reduction, not an unconditional proof of
`RationalSummandBlockCenterStatement`. The missing VI.4.1 theorem remains an
obligation of its existing owner. No claim of task completion is made.
