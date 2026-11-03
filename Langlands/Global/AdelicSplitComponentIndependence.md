# Independence of the chosen split component

Author: Worker 112.

For an arbitrary number field `F : Type u`, an actual group scheme `G/F`
with `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]`, and any two
actual split components `i : T.toGrp → G` and `i' : T'.toGrp → G`, this
module constructs an identity-on-representatives homeomorphism

`splitComponentQuotientHomeomorph F G hi hi' :`
`PositiveRationalQuotient F G T i ≃ₜ PositiveRationalQuotient F G T' i'`.

It also constructs `splitComponentQuotientMeasurableEquiv` with the same
underlying function and proves that this map preserves the exact existing
`positiveRationalQuotientHaarMeasure`. It intertwines positive right
translation by every element of the actual adelic group.

These are internal constructions from the published split-component,
intrinsic-positive-subgroup and quotient APIs. No additional external
structural theorem is used. In particular, the module does not assume
`CentralSplitTorusCharacterStatement`, injectivity or finite index of
character restriction, an adelic positive/norm-one decomposition, or a
choice of splitting coordinates. Connected reductivity of the ambient
group is not needed when the two split components are supplied. Arbitrary
universes and split rank zero are retained.

## Equality of actual positive images

`imageSubgroup_le_of_factor` works even without the affineness and finite
type premises. Given a homomorphism of commutative group schemes
`f : T → T'` such that `groupHom f ≫ i' = i`, it proves containment of the
intrinsic positive images in `G(A_F)`. For a positive point `a` of `T`,
`map_intrinsicSubgroup_le` puts its actual image under `f` in the intrinsic
positive subgroup of `T'`. The stated composite equality identifies that
point's image under `i'` with its original image under `i`.

For `imageSubgroup_eq_of_splitComponents`, the imported theorem
`IsSplitComponent.exists_comp_eq` supplies such a factorization in both
directions: every central split torus factors through either supplied
split component. Its finite-type coordinate-algebra premise follows from
`finiteType_coordinateAlgebra G` under the explicit affine and local
finite type assumptions. Apply the containment theorem to each
factorization, written as a commutative-group morphism using
`Additive.ofMul`, and use antisymmetry. The result is literal equality of
subgroups of the unchanged actual adelic group, rather than a comparison
of substitute point models.

`positiveRationalSubgroup_eq_of_splitComponents` adjoins the same
`rationalSubgroup F G` to these equal subgroups. Since
`positiveRationalSubgroup` is their supremum with the rational subgroup,
this gives literal equality of the two generated subgroups as well.

## Quotient topology, measurable structure and right translation

The generic helper `LeftCosetSpace.congrSubgroupHomeomorph` associates a
homeomorphism to equality of subgroups of a group with a topology. The
construction eliminates the equality and uses the identity homeomorphism.
It therefore sends `[x]` to `[x]`, and commutes with every right translation.
The two `measurable_congrSubgroupHomeomorph` lemmas prove measurability in
both directions by the same equality elimination, now for the inherited
quotient sigma algebras. No Borel identification or separation premise is
needed for this comparison.

Apply these helpers to the proved equality of positive-rational subgroups.
The resulting `splitComponentQuotientHomeomorph_mk` and
`splitComponentQuotientMeasurableEquiv_mk` state the exact representative
formula. The quotients remain the existing left homogeneous spaces,
with the convention `[x] → [x*g]` for positive right translation.
No normality is assumed. The homeomorphism's right-translation formula
uses the same ambient element `g` on both sides.

`splitComponentQuotientMeasurableEquiv_normOneToPositiveQuotient` proves
that the comparison commutes with the existing inclusion from
`NormOneRationalQuotient F G`. Quotient induction reduces this to the
representative formula for the same norm-one point.

## Exact measure comparison

The existing definition `positiveRationalQuotientHaarMeasure` is the
pushforward of the fixed `normOneRationalQuotientHaarMeasure F G` along
`normOneToPositiveQuotient`. This definition itself does not require a
positive/norm-one decomposition. The inclusion map is measurable by
quotient descent of measurable subtype inclusion followed by the target
quotient projection.

`measurePreserving_splitComponentQuotient` composes the two measurable
pushforwards. The preceding commutation formula replaces their composite
by the target's norm-one inclusion, giving exactly the target's defined
measure. There is no rescaling factor. Thus changing the supplied split
component changes neither representatives nor the chosen measure under
the constructed comparison.

This conclusion compares the existing measures at their definition's
scope. It does not independently establish their nonzero, regular,
locally finite, invariant or finite-volume properties. The stronger
properties in `AdelicSplitCenterMeasure` retain their stated hypotheses;
none is silently discharged here.

The construction also does not identify the positive image with the
greatest rational split centre after restriction of scalars in
Getz–Hahn (2.20), or prove independence of any height, reduction domain or
automorphic growth condition. Those comparisons and the unconditional
positive/norm-one decomposition remain separate obligations.
