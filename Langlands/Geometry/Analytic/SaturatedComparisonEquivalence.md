# Actual comparison with enlargement and equivalence of atlas categories

This is an internal consequence of the actual full local-domain enlargement,
the local-domain inclusion category, full saturated bounded composition, and
the full faithful saturation functor constructed in
`CompatibleStrongOriginalRestriction`. It uses the explicit original local
compatibility convention of `CompatibleStrongMaps`. The field is complete,
ultrametric and normed. Its valuation may be trivial. Both the original and
enlarged chart-index types lie in the ambient-space universe `v`.

`AffinoidAtlasPresentation.directToSaturation` and
`directFromSaturation` construct the actual comparison maps in this common
index universe. They use the same full local-domain inclusion constructions
as `AtlasSaturationComparison`, with the original index types themselves.
Their ambient continuous maps are the identity. For every admissible
original-to-enlarged pair, the forward pullback is the bounded restriction
of `originalToSaturatedInclusion`. The reverse uses
`saturatedToOriginalInclusion` on every admissible enlarged-to-original pair.
No containing target is fixed as the sole datum of a map.

The forward target-existence proof uses the enlarged original chart.
The reverse uses the original parent of the enlarged chosen
representative. Ambient-map naturality of local-domain arrows proves the
chart equations, together with the original whole-domain chart equation.
For each two-variable restriction equation, two composites are arrows
with the same local-domain endpoints. Their proved uniqueness identifies
their entire bounded restrictions. Original whole-chart restriction
recovery then identifies the desired original atlas restriction.
The lemmas `directToSaturation_baseMap` and
`directFromSaturation_baseMap` record the literal identity continuous maps.

`isQuasiIso_directToSaturation` and
`isQuasiIso_directFromSaturation` prove the existing full quasi-isomorphism
condition for these maps, even before the original atlas is assumed
saturated. The identity map is a homeomorphism. In each admissible chart
pair, its relative chart-image locus is the inverse image of the source
local-domain locus under the target ambient map. The actual inclusion
arrow's `represents` theorem supplies the full affinoid-test universal
property for this locus.

The two bounded inverse laws additionally assume that the original atlas
has all local full domains. This makes the existing saturated composition
available with either presentation as its intermediate object.
`directToSaturation_comp_directFromSaturation` proves the entire original
composite equal to `StrongHom.id A`. For each original source `i`, it
chooses the enlarged original chart as the intermediate chart and `i`
as the final target. The composition recovery theorem gives the literal
composite of the two bounded pullbacks. Their local-domain arrows compose
to the identity by arrow uniqueness. Applying the restriction function
gives equality with the bounded identity, hence with the original diagonal
restriction. Full saturated extensionality identifies every remaining
admissible pullback.

`directFromSaturation_comp_directToSaturation` proves the entire enlarged
composite equal to its identity. For an arbitrary enlarged source `S`,
choose its original parent `i` and the enlarged original chart `I` of
that parent. The recovered bounded composite is the restriction of the
local-domain arrow through the whole original chart `i`. Uniqueness
identifies this arrow with `saturatedInclusion S I`, whose restriction is
exactly the enlarged identity pullback at this pair. Full saturated
extensionality completes the equality on every admissible target. Both
inverse laws therefore identify full bounded-map families; their proofs
use bounded restriction uniqueness established on all affinoid tests.

`SaturatedAtlasPresentation.saturationIso S` packages these actual
comparison maps as an isomorphism from the constructed enlargement of
`S.presentation` to `S` in the existing saturated category. Its forward
map is the reverse comparison and its inverse is the forward comparison.
The two base-map lemmas identify both with the identity continuous map.

Every saturated object `S` is thus isomorphic to the saturation functor's
value on the compatible object containing `S.presentation`. This proves
the `EssSurj` instance for
`CompatibleAtlasPresentation.saturationFunctor` with index universe `v`.
Together with its previously constructed `Full` and `Faithful` instances,
this gives `IsEquivalence`. The definition
`CompatibleAtlasPresentation.saturationEquivalence` applies Mathlib's
full-faithful essentially-surjective equivalence construction to this
actual functor. Its chosen inverse uses the supplied actual comparison
isomorphisms and the already proved full Hom recovery. The forward
functor is literally `saturationFunctor`, as recorded by
`saturationEquivalence_functor`.

`saturationEquivalence_spaceFunctor` states literal equality with the
original ambient space functor after composing with the saturated
category's ambient space functor. It follows by unfolding the constructed
forward functor, so its original spaces and continuous maps are retained.
The equivalence in this module concerns the stated common index
universe. Analytic localization, etale and quasi-etale sites, equivariant
constructions, compact and distinguished domains, and Harris tower
specializations remain subsequent obligations.
