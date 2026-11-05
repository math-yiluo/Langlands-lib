# Intrinsic positive split-component roots of a specified parabolic

Author: Worker 1457.

This is an internal derived construction from the published
`ParabolicSplitComponentCocharacter`, `ParabolicRootRadicals`,
`SubtorusIntertwiningRoots`, and split-torus weight restriction interfaces.
It introduces no external structural assertion. The complete aggregate
`ParabolicRootPresentationStatement` remains unproved.

Let `r : ParabolicRootPresentation p l a` present the specified actual maps
`p : P → G`, `l : M → P`, and `a : A.toGrp → M`, over any field `k : Type u`.
Assume the ambient structure morphism is affine. The existing defining
cocharacter `r.splitComponentCocharacter` belongs to the specified `A` and
realizes both the supplied parabolic image and supplied Levi image.

`intrinsicPositiveRoots` consists of all actual roots of the action of
`a ≫ l ≫ p` pairing positively with this cocharacter. `intrinsicSimpleRoots`
is the indecomposable part of that positive set, as defined by the existing
`simpleRelativeRoots`. These definitions do not identify the latter set with
restrictions of simple roots from a maximal split torus.

`restrict_mem_intrinsicPositiveRoots` proves that every complementary ambient
simple root restricts to an intrinsic positive weight. Pairing naturality
and the standardness law of the defining cocharacter give a strictly positive
integer pairing, so the restricted character is nonzero. The published actual
`rootRestriction` then gives its nonzero adjoint weight space. Compatibility
identifies the ambient composite with the supplied split-component map.
`restrictedRoots_subset_image_intrinsicPositiveRoots` applies this observation
to every vector in the target's restricted-root set, in the full real character
space of `A`.

Assume also that `G` is smooth. A supplied rational Levi includes an actual
geometric unipotent radical `n : U → P`. For any compatible presentation,
the published `range_comp_radical_eq` identifies the dynamic identity-limit
subgroup of its defining cocharacter with `range (n ≫ p)`. Applying this to
two presentations proves `dynamicUnipotent_splitComponentCocharacter_eq` on
all test schemes. The published complete support formula gives
`intrinsicPositiveRoots_eq_subgroupRelativeRoots` for every supplied such
radical. Using the same radical for two presentations proves
`intrinsicPositiveRoots_eq`. Replacing the positive set in the definition of
indecomposability proves `intrinsicSimpleRoots_eq`.

The comparison permits different maximal split tori, embeddings, generic
cocharacters and simple-root indices. It assumes no ambient root-system,
reflection-existence or conjugacy statement. Arbitrary characteristic,
nonsplit groups, multipliable weights, and rank zero are retained. The
results compare complete positive split-component weights and their
indecomposables; they do not establish equality between those indecomposables
and the target's restricted ambient simple roots. That comparison and general
presentation existence remain outstanding.
