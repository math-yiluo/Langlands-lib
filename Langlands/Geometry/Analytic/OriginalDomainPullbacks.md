# Pullbacks of actual original-chart-domain inclusions

This module constructs the categorical pullback of two original-chart-domain
inclusions in `AffinoidAtlasPresentation`. Its pullback object is the already
constructed actual subspace presentation of their literal intersection.
Coefficients, points and chart indices retain independent universes `u`, `v`
and `w`. The coefficient field is complete and ultrametric; no reducedness
assumption is added.

`originalDomainInclusion_mono` proves monicity on the entire chosen bounded
arrows. Equality after inclusion gives equality of the underlying subtype
values and of the underlying original chart indices. Subtype extensionality
recovers the base maps and index maps. Heterogeneous congruence applied to the
dependent `pullback` field recovers its full bounded algebra maps: composition
with the inclusion's bounded identities preserves that data definitionally.
This proof does not infer algebra-map equality from spectrum points.
`originalDomainMap_mono` then follows by composing a nested inclusion with
its target's ambient inclusion.

For a chosen bounded map `f : Z ⟶ A`,
`Hom.factorOriginalDomain f S hc` constructs its codomain restriction when
every entire chosen original target chart lies in `S`. This is a condition on
the selected charts, stronger than containment of the underlying point image.
`Hom.baseMap_memOriginalDomain` derives pointwise containment from quasinet
coverage of the source and the chart containment of `f`. The factor has the
continuous subtype codomain restriction, the same selected original index
with its containment proof, and exactly the original bounded pullback.
Its chart and restriction equations are inherited from `f`.
`factorOriginalDomain_inclusion` recovers the complete original arrow, and
`factorOriginalDomain_unique` proves uniqueness by monicity.

Suppose `f` maps into `S`, `g` maps into `T`, and their composites into `A`
are equal as complete chosen arrows. For every source chart this equality
identifies their original target indices. Each selected range is therefore
contained in both subsets. `originalDomainIntersection_chart_subset` proves
this fact, and `originalDomainIntersectionLift` factors the ambient composite
through `S ⊓ T`. Its point values and original indices agree with those of
`f`, and its bounded pullbacks are exactly those of `f`. The evaluation,
index and pullback formulas record these equalities.

`originalDomainIntersectionLift_inclusion` recovers the ambient arrow.
The two projection laws, `originalDomainIntersectionLift_fst` and
`originalDomainIntersectionLift_snd`, follow by cancelling the respective
ambient inclusions. They are equalities of complete arrows. Monicity of the
first intersection inclusion already proves uniqueness of the lift.
`originalDomainIntersectionCone` bundles the actual intersection object,
its two bounded inclusions and the published commutative diamond.
`originalDomainIntersectionIsLimit` supplies its limit structure using the
constructed lift, projection laws and uniqueness.
`originalDomainIntersection_isPullback` records the resulting Cartesian square.

These constructions are internal derived consequences of the published
original-chart subspace and chosen-map constructions. Their source conventions
come from Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`: section 1.1,
printed pp.13–14 / PDF pp.10–11 (induced subspaces, contained-member families,
quasinets and nets), and Definition 1.2.3 and Remark 1.2.4(i), printed p.16 /
PDF p.13 (affinoid atlases and bounded restrictions). The categorical
factorization and pullback proved here are internal results, not separately
attributed theorems from that source.

The domains use charts already in a fixed original atlas, and the arrows
retain their selected target indices. This module does not construct arbitrary
analytic domains, saturated atlases, pullbacks of unrestricted strong analytic
morphisms, general analytic fiber products, or an analytic site.
