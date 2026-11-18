# Conditional reflection of étaleness on affine test points

This internal supporting module proves conditional reductions toward
`SpaceAnalytificationEtaleStatement`. Every additional analytic input is a
hypothesis. The module supplies no unconditional proof of that statement.
Its provenance is derived from the Library's definitions, scheme descent,
affine coordinate equivalences, categorical pullbacks, and the published
composition and isomorphism invariance of localized étaleness.

`etale_snd_of_isPullback_of_etalePullbacks` applies the assumed
`LocalizedEtalePullbackStatement` to the two legs of an actual supplied
pullback square. Pullback uniqueness identifies the supplied upper-left
object with the object given by the assumption. Its second projection is
therefore an isomorphism followed by an étale morphism, hence étale.

`ringHom_etale_of_localizedHom_etale` uses the assumed
`AffineAnalytificationEtaleStatement` only in its étale clause. A separate
hypothesis `hRecognition` says that localized étaleness of the actual affine
map implies finite-pieces strong étaleness for that map on its original affine
presentation. This is precisely the predicate in the affine comparison's
étale clause.

The recognition premise remains explicit because the original affine atlas
has index universe `0`, while the existing
`etale_localizationFunctor_map_ofSaturation_iff` takes original atlas index
universe equal to the space universe. Its direct application therefore does
not justify the needed finite-pieces assertion in arbitrary universes. The
separate shared proposal
`AffineAnalytificationLocalizedEtaleReflectionStatement` names this missing
implication; this module retains its type as an explicit hypothesis and
depends only on published imports.

`isEtale_pointHom_of_etale_of_affineReflection` assumes a separated algebraic
space locally of finite type, its supplied analytification, localized étale
pullbacks, and reflection for actual affine algebra maps. For an affine test
point `x` whose analytic map is étale, the theorem applies
`isEtale_of_affine_target_tests`. Given an affine étale target chart `V`, its
actual represented pullback `T` with the source `Spec A` is affine by
separatedness. The finite polynomial presentation makes `A` finite type.
The étale chart is locally of finite type, and the pullback projection to
`Spec A` is étale, so the coordinate rings `B` of `V` and `C` of `T` are
finite type and have finite polynomial presentations.

The canonical affine isomorphisms express the actual two projections as
spectra of algebra maps `f : A → C` and `g : B → C`.
`ringTestMap_affineRingPointEquiv` recovers these scheme maps exactly.
`IsPullback.of_iso'` transfers their represented pullback to the affine-test
square required by `IsAnalytification.isPullback`. In the resulting actual
analytic square, the upper-right leg is the assumed étale map attached to
`x`. The pullback-uniqueness lemma makes the projection corresponding to
`g` étale. Assumed affine reflection makes `g` an étale ring map, and
`HasRingHomProperty.Spec_iff` followed by transport through the affine
isomorphisms makes the actual scheme projection étale. The algebraic
target-chart criterion concludes that `pointHom K x` is étale.

`spaceAnalytificationEtaleStatement_of_sourceDescent_of_affineReflection`
combines this point reflection with the source-descent and finite-type
affine-test reduction in `SpaceAnalytificationEtaleReduction`. The
source-descent family has universe `u + 1`; each algebra and analytic point
carrier has universe `u`. The conclusion is the unchanged published
`SpaceAnalytificationEtaleStatement.{u}`, under three explicit hypotheses:
source descent, localized étale pullbacks over every field, and reflection
for actual affine algebra maps over every field.

`spaceAnalytificationEtaleStatement_of_inputs` replaces the last hypothesis
with two explicit inputs: the affine étale comparison and the original-atlas
recognition premise. Thus its four hypotheses expose the remaining analytic
obligations. The source-descent type is expanded rather than imported from
an unpublished proposition. The theorem is a conditional helper and is not
an exact-target proof submission.
