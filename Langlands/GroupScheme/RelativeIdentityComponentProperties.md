# Uniqueness and normality of relative identity components

This file develops internal consequences of the published all-test
`IsRelativeIdentityComponent` predicate. It constructs compatible comparisons of
representatives and proves all-test normality when a representative is
geometrically connected. All base and test schemes share an arbitrary universe
`u`. There is no affineness, separation, reducedness or finite type assumption.

## Comparisons of representatives

The first declarations belong to
`Langlands.GroupScheme.IsRelativeIdentityComponent`.

`range_eq hi hj` identifies the subgroup functors of two representatives by
applying their factorization criteria on each test scheme.
`iso hi hj` uses the published comparison of monomorphic representatives in
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`. Open immersions supply
the required monomorphisms. `iso_hom_comp` proves compatibility with the two
inclusions.

`geometricallyConnected hi hj` transfers geometric connectedness from the
second representative to the first. The comparison gives a pullback square
with an identity morphism on the base, and geometric connectedness is stable
under this pullback.

## Normality and its proof

The remaining declarations belong to
`Langlands.GroupScheme.RelativeIdentityComponent`.

`conjOver i` is the actual morphism `G ×_S H → G` given on test points by
`(g, y) ↦ g * i(y) * g⁻¹`. `lift_conjOver` proves this formula.

Over a field, `range_conjOver_subset_identitySet i` assumes geometric
connectedness of `H` and puts the image of this morphism in the connected
component of the identity of `G`. Each fibre of the projection
`G ×_k H → G` is connected. The conjugation image of this fibre contains the
identity, because the section induced by the unit of `H` maps to the unit
of `G`. The connected image therefore lies in the identity component.
The ambient group need not be affine, smooth or connected.

`isNormal_of_geometricallyConnected hi` assumes that `i : H → G` represents
the relative identity component and that `H → S` is geometrically connected.
For an arbitrary test scheme and points `g : T → G`, `y : T → H`, pullback
preserves multiplication, inverse and composition. The field lemma applies
to the actual residue-fibre pullbacks. The resulting fibre-image condition
gives factorization of `g * i(y) * g⁻¹` through `i` by `hi.factors_iff`.
This is `(SubgroupFunctor.range i).IsNormal` on every test scheme, including
nonreduced and nonaffine tests.

`smoothNormality_of_existence` proves
`SmoothExistenceStatement → SmoothNormalityStatement` in the same arbitrary
universe. It transfers geometric connectedness from the representative
supplied by existence to any supplied representative and applies the previous
lemma. Smoothness occurs only through the existence premise.

## Provenance and remaining scope

These are derived internal constructions and proofs using the published
representation criterion, the compatible-comparison theorem, Mathlib's
connected fibres of geometrically connected morphisms, and group-object
functoriality. The conjugation argument generalizes the implemented proof in
`Langlands.GroupScheme.IdentityComponent.range_conjOver_subset` to an arbitrary
geometrically connected source subgroup and then to residue fibres.
No new external literature assertion is introduced.

This file does not prove smooth existence or unrestricted base-change
compatibility, and its conditional normality result does not by itself prove
`SmoothStructureStatement`. These remain obligations of the enclosing task.
