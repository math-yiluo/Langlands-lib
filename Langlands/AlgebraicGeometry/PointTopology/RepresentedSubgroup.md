# Closed represented subgroups in the identity-test point topology

Worker 115. This internal topology adapter supports the exact dynamic-Levi smooth-dual finite-length task. It derives the following results from the published point-topology and represented-subgroup constructions.

* `continuous_rationalPointMap`: postcomposition by any morphism between affine schemes is continuous on actual identity-test points, with `rationalPointTopology` on both carriers.
* `isEmbedding_rationalPointMap`: a closed immersion induces an embedding on these points, without a separation assumption on the coefficient ring.
* `isClosedEmbedding_rationalPointMap`: over a Hausdorff coefficient ring this embedding has closed range.
* `isClosed_rationalPoint_subgroup`: if `S` is represented by an actual closed subgroup `i : H → G`, its identity-test carrier is closed in the ambient rational-point group.
* `rationalPointSubgroupHomeomorph`: the published multiplicative point equivalence from `RationalPoint R H.X` onto `S.carrier` is a multiplicative homeomorphism for the representative's own rational-point topology and the subgroup's subspace topology. The application lemma identifies its underlying ambient point with postcomposition by `i`.
* `rationalPoint_subgroup_compactOpenCofinal`: every closed subgroup of the actual point group of an affine, locally finite-type group scheme over any nonarchimedean local field has compact open subgroups cofinal among its open subgroups.
* `represented_rationalPoint_subgroup_compactOpenCofinal`: the preceding conclusion applies when the subgroup is specified by a closed representative.

The coefficient-ring, affine-scheme and represented-subgroup facts have a single arbitrary universe `u`. The local-field results allow both field characteristics and impose no reductivity, splitness or cocharacter condition. They quantify over every supplied `IsTopologicalGroup` instance on the pinned ambient topology. The cofinality conclusion uses exactly the subspace topology, with no separate topology on the subgroup.

The first three proofs express postcomposition through the published `rationalPointHomeomorph` comparisons. Under these comparisons the map is the existing `RingPoint` postcomposition map. The continuity and embedding results therefore follow by composing the homeomorphisms with `continuous_affineSchemePointMap`, `isEmbedding_affineSchemePointMap` and `isClosedEmbedding_affineSchemePointMap` from `AffineSchemeMapProofs`.

For the fourth result, affineness of `H` follows from the closed immersion into affine `G`. The representation equation identifies `S.carrier` with the range of the closed embedding on actual points. Its range is closed. The homeomorphism uses the existing `SubgroupFunctor.IsRepresentedBy.pointsEquiv`; its composite with subtype inclusion is that same point embedding. Since subtype inclusion is inducing, the point equivalence is inducing and hence a homeomorphism. Its multiplication law is the original represented-subgroup law.

For compact-open cofinality, the ambient group is locally profinite by the published `BruhatTits.rationalPoint_isLocallyProfinite` in `BruhatTits.Unipotent.RationalPointCompactOpen` (Worker 399, using Worker 105's `RationalPointGroups`). A closed subgroup inherits local compactness, Hausdorffness and total disconnectedness. The published `Topology.LocallyProfiniteProof.vanDantzig` then supplies a compact open subgroup inside each given open subgroup. The final corollary supplies closedness using the fourth result.

This is an internal derivation, with no separate external source-translation claim. It does not construct a closed representative or prove connected reductivity for every dynamic centralizer. Those facts, the admissibility theorem, and the final exact finite-length target remain separate obligations. The helper explicitly takes represented-subgroup data where required; none of it is represented as an unconditional proof of the dynamic-Levi target.
