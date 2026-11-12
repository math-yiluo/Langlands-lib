# Smooth subgroup restriction and the original point stalk

This constructs the smooth subgroup and point restrictions in Renard 2026,
III.3.2, printed p.84 / PDF p.90, from the published algebraic functors.
The category uses Renard's smoothness of **all** compact global sections,
not a supplied smoothness assumption on the stalk or the smooth part of it.

All names have prefix `Langlands.Sheaf.Renard.SectionActions`.

`isSmoothAction_subgroupRestriction` identifies the compact-section action
of the existing `subgroupRestriction` with continuous pullback of the
original compact-section representation along the subgroup inclusion.
The published `Langlands.isSmooth_comp` proves the property needed by
`smoothSubgroupRestriction`. That functor is the full-subcategory lift of
the original subgroup restriction and retains its original sheaf maps.

For any subgroup `Q` fixing `x`, `fixedStalkCompactGerm` is the actual global
germ map on the original compact-section space, valued in the original
neighborhood-colimit stalk with the action of `fixedStalkFunctor`.
Its equivariance follows from the published
`Godement.germ_stalkPull_arrow` applied to the original inverse-labelled
global section arrow. Thus it intertwines the subgroup pullback of the
compact-section representation with the original fixed-stalk action,
with exactly the same left-action convention as `StalkActions`.

If `X` is `Langlands.Topology.IsLocallyProfinite`,
`fixedStalkCompactGerm_surjective` uses `CompactGerms.germ_surjective`:
every original stalk element is represented by a compact global section
using the published clopen zero extension. The published continuous-pullback
and equivariant-surjection smoothness results then give
`isSmooth_fixedStalk`. These are the intrinsic laws required to define
`smoothFixedStalkFunctor`, Renard's point restriction into `M(Q)`.
It uses the entire original stalk. There is no new stalk object,
quotient surrogate or assumption of the desired smoothness conclusion.

`smoothFixedStalkToRepIso` identifies the functor after forgetting smoothness
with the existing original-stalk functor. The representation and map formulas
state literally that its action and its morphisms are the published original
stalk action and induced stalk maps.

The base action is jointly continuous, the group universe is arbitrary,
and the actual complex coefficient field, base and section carriers are in
universe zero, as in the existing compact-support interface. The point
construction assumes a Hausdorff compact-open neighborhood basis on `X`.
The group may be any topological group carrier admitting the stated action;
neither closedness of `Q` nor local compactness of `G` is needed for these
specific constructions, since continuous restriction along any subgroup
preserves smoothness. Renard's t.d. group and closed-subgroup case is included.
No transitive homogeneous-space assertion is made, so there is no use or
omission of its separate countability-at-infinity hypothesis here.
General locally closed subspace restriction and its comparison with the
point construction remain separate obligations of III.3.2.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.3.2, printed p.84 / PDF p.90,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
