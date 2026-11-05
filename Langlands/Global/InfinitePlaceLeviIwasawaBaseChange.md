# Actual completion transport for Levi-compatible Iwasawa decompositions

Author: Worker 1655.

This internal derived prerequisite transports all four conclusions of the
published `InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement` between
actual completion-valued points and actual points of the completion pullback.
It does not construct the compact subgroup or prove that existence statement.

`CompactIwasawa.IsMaximalCompact` records compactness and maximality among all
compact overgroups. Its `map` theorem transports both properties along a
multiplicative homeomorphism. A compact overgroup of the mapped subgroup pulls
back to a compact overgroup of the original subgroup; maximality and
surjectivity then give equality.

`IsLeviCompatibleDecomposition p m K` records maximal compactness of `K`, the
literal covering `range p * K = univ`, equality of the parabolic and Levi
intersections with `K`, and maximal compactness of `K.comap m` on the Levi
carrier with its given topology. `HasLeviCompatibleDecomposition` existentially
quantifies `K`. The ambient, parabolic and Levi carriers have independent
universes. The parabolic carrier needs only a group structure; the ambient
and Levi carriers have their own topologies.

The transport theorem uses commuting comparisons for both homomorphisms.
The ambient and Levi comparisons are multiplicative homeomorphisms, while the
parabolic comparison is a multiplicative equivalence. Covering transports by
decomposing the inverse image of each target point and applying the ambient
comparison. The intersection equality transports by injectivity of that
comparison. `comap_map_eq_of_comm` identifies the transported inverse-image
subgroup with the image of the original Levi inverse-image subgroup. Applying
the Levi homeomorphism therefore preserves its compactness and unrestricted
maximality. The equivalence theorem repeats the argument with inverse
comparisons.

The two actual-point predicate comparisons are reflexive: the generic
formulations reproduce precisely the published compact and four-conclusion
predicates. The completion equivalence uses the published
`completionBaseChangeHomeomorph` separately for the ambient group and the
Levi, and `affinePointsBaseChangeMulEquiv` for the parabolic. The actual point
map naturality identities apply to `p` and to the composite `l ≫ p`; functoriality
identifies the latter pullback map with the composite of the pulled-back
maps. Both topologies are the existing regular-function evaluation topologies.
Affineness is required of the ambient and Levi schemes for these
homeomorphisms; the existing connected-reductive premises supply it in the
intended application. No claim of preservation of the rational-Levi predicate
under field extension is made here.

`isClosedEmbedding_leviPoints` proves that the actual composite `l ≫ p` induces
a closed embedding on completion-valued points. The supplied parabolic and
rational-Levi predicates give closed immersions, their composite is closed,
and the reductive ambient and Levi schemes are affine. The published
closed-immersion point theorem then applies to the actual Hausdorff completion.
`isCompact_comap_leviPoints` pulls compactness back along this closed embedding.
It uses the topology of the actual Levi carrier. This last result alone does
not assert maximality of the inverse image of an arbitrary ambient maximal
compact; the compatible compact construction must still establish maximality.

The provenance is elementary subgroup, set-image and compactness reasoning,
the published actual-point base-change homeomorphism and naturality, and the
published affine closed-immersion point theorem. No new external literature
assertion is used. General archimedean compact existence, compatibility with a
specified Levi, and any required local algebraic standard-pair construction
remain obligations of the full proof task.
