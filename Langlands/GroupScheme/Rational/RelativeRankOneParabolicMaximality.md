# Maximality from roots on a Levi split component

This internal development for Task 5515 addresses the maximality
condition in a rational rank-one wall. `HasProportionalRootPairings i`
requires vanishing cross determinants for the integral pairings of every
two actual roots of the specified split torus.

The proof first places every containing rational parabolic in the split
component of the original Levi. A compatible root presentation provides
a common ambient maximal split torus. The defining cocharacter of the
containing parabolic lies in the original Levi; since the whole Levi lies
in its parabolic, reductivity forces this cocharacter to be central in
the Levi. It therefore factors through its specified split component.

For two defining cocharacters in that component, proportionality of all
root pairings shows that the containing dynamic parabolic is equal to the
original one or is the whole group. A proper dynamic parabolic has a
positively pairing root: otherwise the negative cocharacter defines the
whole group, and reductivity forces its centralizer, and hence also the
original parabolic, to be the whole group. Fixing that positive root, a
zero pairing at the second cocharacter forces all its root pairings to be
zero. A positive pairing makes all nonnegative root supports agree.
Finally equal subgroup images give an inclusion-compatible isomorphism,
and a full image makes the containing subgroup map an isomorphism.

The material is derived from the imported structural proofs and the
elementary pairing argument described here. It does not assert existence
of a finite gallery or a representation-theoretic conclusion.

The declaration
`ParabolicRootPresentation.exists_splitComponentCocharacter_of_parabolic_le`
assumes a compatible presentation of the original parabolic, its specified
rational Levi and split component, and connected reductivity of the ambient
group. Its conclusion presents every containing rational parabolic by an
integral cocharacter of that same split component. It uses the published
`parabolicDynamic`,
`exists_parabolic_eq_cocharacter_of_parabolic_le`,
`smoothMaximalSplitTorusConjugacy`, `dynamicSmooth`, `dynamicConnected`,
`Dynamic.torusFactor`,
`Dynamic.parabolic_eq_comap_of_isClosedSubgroup`,
`Dynamic.parabolic_eq_top_iff_centralizer_eq_top`, and
`IsSplitComponent.exists_factor`.

`RelativeRoot.exists_pairing_pos_of_parabolic_ne_top` and
`RelativeRoot.parabolic_eq_or_top_of_proportional_pairings` implement the
pairing argument. They use splitness of the specified torus, connected
reductivity of the group, and the published comparisons
`Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots`,
`Dynamic.centralizer_groupHom_neg`,
`RelativeRoot.nonnegative_rootSupport_of_parabolic_le`, and
`RelativeRoot.parabolic_le_iff_nonnegative_rootSupport`.

The final theorem
`isMaximalParabolic_of_proportional_splitComponent_pairings` assumes an
actual rational parabolic `p`, a specified rational Levi `l`, its specified
split component `a`, properness expressed as `¬ IsIso p`, and
`HasProportionalRootPairings (a ≫ l ≫ p)`. It concludes that any factor map
`f` into any containing rational parabolic `h` is an isomorphism or `h` is
an isomorphism. It obtains the compatible presentation from
`parabolicRootPresentationExistence` and the original defining cocharacter
from `ParabolicRootPresentation.exists_splitComponentCocharacter`.
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` identifies equal
images, while `isIso_of_full_range` treats the full image. Cancellation is
performed on the monomorphism over the base induced by the actual closed
subgroup inclusion. The proportionality hypothesis concerns roots on the
Levi split component; it makes no rank claim about a larger maximal split
torus.
