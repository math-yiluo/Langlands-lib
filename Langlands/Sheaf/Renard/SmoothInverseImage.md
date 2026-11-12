# Smooth inverse image and subgroup-space restriction

Worker 151. Construction supporting Renard III.3.2, printed p.84 / PDF p.90
of the French edition dated 9 July 2026. The source restricts smooth action
sheaves along a closed subgroup and a locally closed invariant subspace.
This unit lifts the existing actual inverse image to Renard's smooth-action
category; the construction works for any continuous equivariant space map.

The group, spaces, coefficients and section carriers are in `Type`, as required
by the existing action inverse-image and direct-image coreflector interfaces.
The group is a topological group and both space actions are jointly continuous.
The source base of the inverse-image functor is Hausdorff locally profinite;
the target base does not need this additional condition for the construction.

`inverseImageToSmooth` uses the actual `actionInverseImageAdjunction`, not a
replacement inverse-image object. It factors the adjunction unit from a locally
smooth sheaf through the local smooth subsheaf of its direct image, using
`smoothLift`. The published `SmoothDirectImage.preimageSmoothMap` then maps to
the direct image of the actual inverse image's smooth subsheaf. Transposition
produces a map from the full inverse image to that subsheaf.

`inverseImageToSmooth_inclusion` proves that this map followed by the original
smooth inclusion is the identity: transpose naturality reduces the equation
to the two published factorization equations and the adjunction unit law.
The map is therefore a split monomorphism into a locally smooth sheaf.
`isSmoothSheaf_actionInverseImage` applies the published smoothness transfer
along monomorphisms. Thus the entire actual inverse image is smooth.

`isSmoothAction_actionInverseImage` derives stable neighbourhoods from the
Hausdorff locally profinite group using `LocalSmoothComparison`, converts the
source Renard condition to local smoothness, applies that construction, and
converts back using the published compactness theorem.
`smoothActionInverseImage` lifts the original functor by this proved property.
`smoothActionInverseImageToActionIso` records the unchanged underlying functor.

`isSmoothAction_subgroupSpaceRestriction` derives local profiniteness of the
closed subgroup from the published locally closed subspace theorem, combines
smooth subgroup restriction with the smooth actual inverse image, and proves
the smoothness needed to define `smoothSubgroupSpaceRestriction`.
`smoothSubgroupSpaceRestrictionToActionIso` identifies its underlying functor
with the original `subgroupSpaceRestriction`. For Renard's locally closed
inclusion it is the requested restriction functor. No countability assumption
is used. Its comparison with the original ordinary restriction stalks remains
separate.
