# A prescribed-torus dynamic presentation cover

This internal construction assembles actual prescribed-torus presentations
into an étale cover over an arbitrary scheme. It reuses
`RelativeLevi.TorusDynamicPresentation` from `TorusLeviLocal` and
`RelativeLevi.SplitTorusDynamicNeighbourhoodData` from
`SplitTorusDynamicNeighbourhood`.

Let \(S\) be a scheme, \(G/S\) a reductive group scheme,
\(i:P\to G\) a relative parabolic, and \(t:T\to P\) a homomorphism
from a commutative group scheme that is a relative torus. Assume that \(t\)
is maximal on every residue fibre of \(P\).
`RelativeLevi.torusDynamicPresentationCover` returns an actual small étale
cover \(\mathcal V\) of \(S\), together with a
`TorusDynamicPresentation` on each member. This contains an actual
cocharacter into the direct pullback of the original \(T\); its composite
through the pulled-back \(t\) and \(i\) dynamically presents that
pulled-back parabolic inclusion. The certificate includes monicity and
equality of subgroup functors on every further relative test scheme.
No reducedness, connectedness or local hypothesis is imposed on the base.
The supplied torus and its homomorphism into the parabolic are retained.

The implemented construction begins with the splitting cover given by the
relative-torus predicate. The lemma
`IsFibrewiseMaximalTorus.comp_relativeParabolic` gives ambient fibrewise
maximality of \(t\) followed by \(i\). Its arbitrary-base-change
transport gives maximality at each residue point of a splitting chart.
Reductivity and relative parabolicity are transported along the actual
chart map. `splitTorusDynamicNeighbourhood` then chooses an open
neighbourhood and a prescribed-torus cocharacter at every point of each
chart. Its field classification, cocharacter lifting, and persistence
argument are implemented in the separate neighbourhood module.

`SplitTorusDynamicNeighbourhoodData.presentation` packages the retained
cocharacter and certificate as `TorusDynamicPresentation`.
`SplitTorusDynamicNeighbourhoodData.cover` forms the point-indexed open
cover from a neighbourhood family; the retained point-lifting witnesses
prove coverage and each open immersion is étale.
`torusDynamicCoverOfNeighbourhoods` binds these covers to the splitting
cover. Its index type remains in universe `u`.

For each resulting member, `TorusDynamicPresentation.direct` composes
the local cocharacter with the canonical comparison from the iterated
pullback of the torus to its direct pullback. Naturality for \(t\)
and \(i\) identifies the ambient composite with the original local
cocharacter followed by the ambient comparison. The published
`isRepresentedBy_dynamicParabolic_direct` transports the complete
representation certificate, including monicity, to the direct pullback
of \(i\). No equality of subgroup schemes is inferred from equality
on residue fibres.

The provenance is internal composition of the cited Library interfaces;
this module makes no independent transcription claim. It constructs
presentation data and does not construct a Levi subgroup or a conjugator.
The exact statement proofs consuming this data are separate contributions.
