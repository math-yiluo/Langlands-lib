# Point data for compatible actual common-Levi presentations

This internal adapter belongs to the proof of actual common-Levi rational
continuation existence. It composes published structural facts; it does not
prove Waldspurger IV.1.1 or the presentation-level analytic reduction.

`PresentationPointData` bundles the source point decompositions, subgroup
closedness, both factorization witnesses and continuity of both projections.
Both decompositions use the first presentation's literal point Levi. The
record also contains an actual `Fintype` enumeration of the relative Weyl
group. The definition `presentationPointData` constructs this bundle from
the all-test realization witnesses and original dynamic data. It has no
analytic premise.

`commonLeviContinuationExists_of_presentations` assumes the two explicit
propositions `DynamicCommonLeviPresentationReductionStatement` and
`ConditionalParabolicIntertwiningStatement`, together with the compatible
scheme presentations and all-test realization witnesses used by the former.
It constructs the preceding point-data bundle and supplies its fields to the
reduction. Its conclusion is `CommonLeviContinuationExists` for the original
compact open subgroup, both original factorization proofs and the original
inducing representation. The carrier universe is independent of the field
universe.

The all-test equalities imply literal equalities of the point parabolics,
common Levi and radicals through `parabolicPoints_eq`, `leviPoints_eq` and
`radicalPoints_eq`. The bundle construction transports `commonDecomposition`
through these equalities. It also transports `radical_isClosed` and
`DynamicOppositeCanonicalScalar.parabolic_isClosed`.
An internal equality-elimination lemma transports
`commonProjection_continuous` to the source projections; proof irrelevance
identifies the decomposition witnesses.

For each supplied factorization, the identity of ambient subgroup elements
`subgroupHomeomorphOfEq` supplies the source parabolic element, preserving the
original compact factor. The finite relative Weyl group follows from
`IsConnectedReductive.finite_relativeWeylGroup` at the maximal split torus of
the first complete root presentation; `Fintype.ofFinite` provides the required
enumeration. The final step applies the stated presentation reduction.
Its reconstructed factorization proofs are propositionally irrelevant, so its
conclusion has exactly the original witnesses.

The source-level analytic target comes from J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
2003, IV.1.1, printed pp. 276–278, registered as
`waldspurger-2003-plancherel`. This module adds no independent claim about that
theorem: both analytic propositions remain premises here.
