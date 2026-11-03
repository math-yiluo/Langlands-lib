# Actual real identity-component image of a rational split central torus

Author: Worker 112.

For a supplied affine commutative group scheme `T` over `Spec ℚ`, an actual
group-scheme map `i : T.toGrp ⟶ G`, and a supplied finite splitting of `T`,
this module identifies the ambient image of the actual real identity
component with `PositiveRealTorus.imageSubgroup ℚ T G i`. When `i` is central,
the subgroup defining the existing positive-rational quotient consists
exactly of products of such real images and principal rational points.
The underlying ambient group and quotient remain the existing actual
adelic points and left coset space.

This is derived internal infrastructure. The proofs use the actual
real-to-adelic comparison, intrinsic positive subgroups, affine-point maps,
and finite-type split-component factorization already constructed in the
Library. No new assertion from the automorphic literature is attributed
to this module.

## Naturality of the actual real-to-adelic map

`RationalRealAdelicPoints.full_naturality` applies to affine group schemes
`H` and `G` over the rationals and any actual group-scheme map `f : H ⟶ G`.
It proves that applying `f` on adelic points after `full H` agrees with
applying `f` on real points before `full G`.

The proof uses the injectivity of the actual infinite/finite point
decomposition. In each projection, applying `f` commutes with coefficient
extension: on actual scheme points, both expressions are the same
composite, by category associativity. At infinity this leaves naturality
for the real coefficient embedding. At finite places both maps take the
inserted identity point to the identity. The proof uses explicitly typed
adele projection algebra homomorphisms.

## Actual positive real points in an ambient group

The real point topology is the existing regular-function evaluation
topology `affinePointsTopologicalSpace`. The ordered-coefficient subgroup
`orderedCoefficientPositiveSubgroup ℚ T ℝ` consists of actual real points
whose every rational character has positive real value. It is defined
independently of splitting coordinates.

`PositiveRealTorus.ambientRealPositive G T i` is a continuous group
homomorphism from this subgroup to `AdelicGroupPoints ℚ G`. It composes
`realToAdelic T` with the existing continuous point map induced by `i`.
Its definition uses affineness of `T` and does not require centrality, a
splitting, or injectivity of `i`. The ambient map also does not require
affineness of `G`. In the subsequent comparison with `full G`, the ambient
group is explicitly assumed affine.

`ambientRealPositive_apply` records this composite on the underlying
points. `ambientRealPositive_eq_full` uses the preceding naturality
theorem to rewrite it as `full G` applied to the actual image under `i`
of the positive real point.

For `I : Type` finite and an actual splitting
`e : T.toGrp ≅ splitTorus (Spec ℚ) I`, `range_ambientRealPositive` proves
equality of its group image with `imageSubgroup ℚ T G i`. The latter is
independently defined as the image under `i` of the intrinsic positive
adelic subgroup of `T`. Both directions follow from the existing exact
range equality for `realToAdelic T`. This range theorem needs no
affineness of `G`.

`ambient_full_image_connectedComponent_one` identifies the set image of
`connectedComponent (1 : Lie.AffinePoints T.toGrp ℝ)` under the map
`a ↦ full G (pointMap ℚ T.toGrp G ℝ i a)` with the underlying set of
`imageSubgroup ℚ T G i`. The proof substitutes the established equality
of the actual real component and intrinsic real positivity, then uses
the range theorem and the naturality formula. It does not stipulate a
new identity component or replace actual points by a parameter model.

All rational specializations in this module use universe zero. The
splitting index may be empty, so split rank zero is included.

## The subgroup defining the existing quotient

`imageSubgroup_le_center` assumes actual scheme centrality `IsCentral i`.
It proves that the positive adelic image is contained in the centre of
the ambient actual adelic group. The all-test centrality hypothesis
applies directly to the adelic coefficient algebra. This argument needs
no affineness, finite type, splitting, or character-detection hypothesis.

`positiveRationalSubgroup_eq_realImage_sup` identifies the existing
subgroup with the supremum of the actual positive-real group image and
the unchanged `AdelicGroupPoints.rationalSubgroup ℚ G`. It follows by
the range equality and the definition of `positiveRationalSubgroup`.

Under `IsCentral i`, `mem_positiveRationalSubgroup_iff_real` states that
membership of `x` is equivalent to existence of an actual real point
`a` in the identity component and an actual rational point `q` such that

`full G (pointMap ℚ T.toGrp G ℝ i a) * rational ℚ G q = x`.

Centrality makes the positive image normal. The subgroup-supremum
membership theorem for a normal left factor then expresses membership
as a product. Substitute the proved real-component image equality for
the first factor and the defining range of principal rational points
for the second. This proves both directions without character-restriction
injectivity or finite-index assumptions.

Thus the subgroup in the existing `PositiveRationalQuotient` has this
actual real-component-times-principal description. The quotient keeps
its existing left coset topology, measurable structure and positive
right action `[x] ↦ [x*g]`; no quotient-group normality is asserted.

## Containment for a supplied split component

`imageSubgroup_le_of_centralSplitTorus` additionally assumes that `G` is
affine and locally of finite type over the rationals, and that `i` is
an actual `IsSplitComponent`. For any central split torus `i'` into the
same group, its intrinsic positive adelic image is contained in the
image of `i`. No affineness of the torus sources is needed here.

The proof obtains a factorization `f ≫ i = i'` from the published
`IsSplitComponent.exists_comp_eq`, using
`finiteType_coordinateAlgebra G`. Regard `f` as a commutative-group
scheme map and apply the existing `imageSubgroup_le_of_factor`.
This proves containment of actual adelic subgroups, rather than only
an abstract comparison of tori.

## Remaining scope

The module takes a rational torus, its splitting and its ambient map as
inputs. It does not construct restriction of scalars for an arbitrary
number-field group, identify its greatest rational split central torus,
or compare the resulting adelic points with the original number-field
adelic group. These remain necessary for the full general-number-field
identification in Getz–Hahn (2.20).

No injectivity or closed-embedding assertion is made for an arbitrary
ambient map `i`. The supplied split-component containment does not
construct a split component or identify a supplied torus with a chosen
centre object. Measures, unconditional positive/norm-one decomposition,
height independence, reduction theory, finite volume and the remaining
automorphic comparisons remain separate obligations.

The local topology instances have explicit names and expose exactly
`GroupScheme.affinePointsTopologicalSpace` on the actual affine-point
carriers. Their definitions and local scope are unchanged.
