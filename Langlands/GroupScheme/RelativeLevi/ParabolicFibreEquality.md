# Equality of relative parabolics from residue fibres

Worker 653.

This is a derived, internal reduction for the uniqueness step in the proof of
Conrad, *Reductive group schemes* (2014), Proposition 5.2.12, p.158. It supplies
supporting lemmas and does not prove `RelativeParabolicLieContainmentStatement`.
The two parabolic comparison lemmas take that statement as an explicit hypothesis.

`SubgroupFunctor.le_range_of_forall_exists_open` says that a subgroup functor
is contained in the image of a monomorphism if the containment holds after
restriction to a Zariski neighbourhood of every point of the base. The proof
chooses these neighbourhoods as an open cover and applies the Library's
`SubgroupFunctor.le_range_iff_baseChange_openCover`. The cover and the base may
be arbitrary; no quasi-compactness assumption is used.

`relativeParabolic_range_le_of_residueFiber_lie_le` applies the assumed
`RelativeParabolicLieContainmentStatement` at each point and globalizes the
resulting local inclusions. Its hypotheses are exactly those of the assumed
statement, with Lie containment required at every residue fibre. In particular,
the two relative parabolics contain the supplied common maximal torus.

`relativeParabolic_range_eq_of_residueFiber_range_eq` assumes instead that
the images of the two relative parabolics agree on every residue-field fibre.
Equality gives both Lie containments. Applying the preceding lemma in the two
directions gives equality of the original subgroup functors.

This implements the reduction to fibres used in the uniqueness argument of
Proposition 5.2.12. The input is Corollary 5.2.7(2), first assertion, p.155,
encoded by the unchanged published `RelativeParabolicLieContainmentStatement`.
All conclusions are equalities or inclusions of subgroup functors on every
test scheme, including nonreduced tests, over an arbitrary base scheme.
