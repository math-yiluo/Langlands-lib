# Homomorphisms from unipotent group schemes to split tori

Worker 1326 adapted the coordinate argument authored by Worker 207 in the
published `Torus.SplitReductiveProof` module. This is an internal consequence of
that module's coordinate representation construction and the existing
`IsUnipotent` definition; it makes no new literature assertion.

Let `k` be any field in universe `u`, let `H` be a group scheme over `Spec k`
with `IsUnipotent H`, and let `G` be a split torus over `Spec k`. The construction
`IsUnipotent.uniqueHomToSplitTorus` equips `H ⟶ G` with `Unique`, whose default
is the trivial homomorphism. Neither closedness of a map nor smoothness,
connectedness, affineness or normality of its source is a premise.

`IsUnipotent.comp_eq_one_of_isSplitTorus` proves identity-valuedness on every
scheme `T` over `Spec k`. Choose an isomorphism from `G` to a split torus indexed
by a finite type `I`. For each coordinate of a homomorphism `f : H ⟶ G`, the
published `splitTorus.coordinateRepresentation` is a one-dimensional matrix
representation. Unipotence gives a nonzero fixed vector. Its unique coordinate
is nonzero in `k`, so its image in the ring of global functions on `T` is a unit.
The fixed-vector equation then forces the corresponding coordinate of `f(y)`
to be one. The point equivalences are injective and preserve identity, giving
`y ≫ f.hom.hom = 1` for every `y` and every `T`.

`IsUnipotent.range_eq_bot_of_isSplitTorus` identifies the pointwise image subgroup
functor with the identity subgroup functor. This uses the same test scheme for
each lift, exactly as in `SubgroupFunctor.range`.
`IsUnipotent.hom_eq_zero_of_isSplitTorus` evaluates identity-valuedness at the
identity morphism of `H.X`, proving equality of the actual homomorphism with the
categorical zero morphism. These results supply the uniqueness field of
`uniqueHomToSplitTorus`.

Finally, `IsUnipotent.comp_eq_zero_of_isSplitTorus` says that every composite
from `H` through a split torus is trivial, with no condition on the receiving
group scheme or the second map. This is the vanishing step used after a
unipotent subgroup has been shown to factor through a split torus. It supplies
no containment theorem for intersections of Borel subgroups and does not prove
the unrestricted dynamic-centralizer reductivity statement.

`IsUnipotent.range_eq_bot_of_range_le_isSplitTorus` assumes monomorphisms on
the underlying schemes over `Spec k` for `f : H ⟶ G` and `i : T ⟶ G`, with
`T` split and `range f ≤ range i`. The published
`SubgroupFunctor.factorOfRangeLE` constructs `g : H ⟶ T` with `g ≫ i = f`.
The preceding vanishing result makes this composite zero, so `range f = ⊥`
on all test schemes. In particular, this applies to closed subgroup inclusions;
the lemma itself asks only for the displayed monomorphisms and inclusion.
