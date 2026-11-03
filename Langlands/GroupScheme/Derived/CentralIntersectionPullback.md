# The pullback representative of the centre inside a subgroup

Author: Worker 846.

This module constructs the closed representative used for
`DerivedCentralIntersectionFinitenessStatement.{u}`. It also reduces that
proposition to finiteness of one pullback. It proves no finiteness itself.

## Range and closedness of the pullback projection

Fix a base scheme `S`, group schemes `D`, `G` and `Z` over `S`, and
homomorphisms `d : D ⟶ G` and `z : Z ⟶ G`. The published
`subgroupIntersection d z` is the fibre product `D ×_G Z` as a group scheme.
`subgroupIntersectionFst d z` is its projection to `D`.

- `range_subgroupIntersectionFst` proves on every test scheme `T` over `S`
  that the range of `subgroupIntersectionFst d z` is
  `(SubgroupFunctor.range z).comap d`. A point `x : T ⟶ D.X` factors through
  the projection exactly when `x ≫ d` factors through `z`. One direction
  composes with the second projection and uses the pullback square. The other
  uses the pullback lift given by `subgroupIntersection_isPullback`.
- The shared `isClosedSubgroup_subgroupIntersectionFst`, imported from
  `SubgroupIntersection`, proves that the projection is a
  closed subgroup when `z` is one. It pulls back the closed immersion `z`
  along `d`, using `subgroupIntersection_isPullback_scheme` and the stability
  of closed immersions under base change (`MorphismProperty.of_isPullback`).
- `range_subgroupIntersectionFst_of_isSchemeTheoreticCenter` combines the first
  lemma with the range clause of `IsSchemeTheoreticCenter z`. The range of the
  projection is then `(center G).comap d`. This is the full inverse image of
  the all-test centre functor. No reduced or rational-point substitute is used.

## Reduction of the target

`derivedCentralIntersectionFiniteness_of_isFinite_subgroupIntersection`
assumes the following hypothesis. For every field `k : Type u`, group schemes
`G`, `D`, `Z` over `Spec k`, and homomorphisms `d`, `z`, if `G` is connected
reductive, `d` is a derived-subgroup inclusion and `z` is a scheme-theoretic
centre, then `(subgroupIntersection d z).X.hom` is finite. From this it proves
`DerivedCentralIntersectionFinitenessStatement.{u}`.

Given `k`, `G`, `D`, `d`, the published `schemeTheoreticCenterExistence`
provides a centre representative `z : Z ⟶ G`. The witnesses are
`C := subgroupIntersection d z` and `c := subgroupIntersectionFst d z`. The
lemmas above give closedness and the range equality. The hypothesis gives
finiteness of `C.X.hom`. The hypothesis is discharged in
`Langlands.GroupScheme.Derived.CentralIntersectionReduction`.

The universe `u` stays arbitrary, and no assumption on `k`, `D` or `d` is
added. The representative is the scheme-theoretic fibre product, so any
nonreduced structure is retained.
