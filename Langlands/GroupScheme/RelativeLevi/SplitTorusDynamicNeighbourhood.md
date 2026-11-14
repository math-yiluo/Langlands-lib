# Dynamic parabolic neighbourhoods through a prescribed split torus

This internal construction assembles published field classification, split-torus
cocharacter extension, and persistence of a prescribed dynamic presentation.
It supports the local presentation step in relative Levi constructions.

Let \(S\) be any scheme, \(G/S\) reductive, and \(i:P\to G\) a relative parabolic.
Fix a commutative group scheme \(T/S\), a homomorphism \(t:T\to P\), a proof that
\(T\) is split, and a point \(s\in S\). Assume that the residue fibre of
\(i\circ t:T\to G\) is a maximal torus of \(G_{\kappa(s)}\).

`RelativeLevi.exists_open_torusDynamicPresentation_of_splitTorus` proves that
there is an open immersion \(p:U\to S\) whose image contains \(s\), and a
cocharacter \(\nu:\mathbf G_{m,U}\to T_U\), such that the pulled-back inclusion
\(i_U:P_U\to G_U\) represents the dynamic parabolic of
\(\nu\) followed by \(t_U\) and \(i_U\). The representation certificate includes
monicity and equality of subgroup functors on every test scheme over \(U\).
The construction applies to arbitrary, possibly nonreduced and disconnected,
bases. Maximality is assumed only at the chosen residue point.

`RelativeLevi.SplitTorusDynamicNeighbourhoodData` retains the actual neighbourhood,
its projection and point coverage, the cocharacter into the pullback of the
specified torus, and the representation certificate.
`RelativeLevi.splitTorusDynamicNeighbourhood` chooses such data under the
hypotheses above.

The implemented proof first applies
`exists_fixedTorusDynamicPresentation_of_isParabolicSubgroup` to the residue
parabolic and the supplied ambient maximal torus. Containment follows from the
factorization through \(P\). It then lifts this actual torus cocharacter using
`IsSplitTorus.cocharacterLattice_baseChange_surjective_field` and composes its
lift with \(t\), obtaining a cocharacter of \(P\). The compatibility theorem
`baseChangeCocharacter_torus_comp` identifies its residue presentation with the
one just constructed. Reductivity and the relative parabolic hypotheses supply
smoothness, affineness and geometrically connected fibres.

`Dynamic.exists_local_presentation_of_fieldPoint` now gives an open neighbourhood
carrying that prescribed source cocharacter and equality of subgroup functors.
Its lift of the canonical residue point proves that the image contains \(s\).
Finally, functoriality of cocharacter base change gives the normalized composite
through \(T_U\), and base change of the monic inclusion supplies the full
`IsRepresentedBy` certificate.

This is a derived internal assembly result; it makes no independent
literature claim. Its geometric inputs are the already published results in
`RelativeLevi.FieldLieContainment`, `Torus.FieldCocharacterExtension`,
`RelativeLevi.ParabolicSourceGeometry`, and `Dynamic.LocalPresentation`, imported
through `RelativeLevi.SplitTorusContainment`. Constructing an étale cover and
transporting iterated pullbacks to direct pullbacks are separate steps.
