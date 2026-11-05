# Actual centralizer maps and full V6 under central-isogeny pullback

This is an internal derivation from the published all-test torus centralizer,
represented-subgroup factorization, rational-character valuation, and normalized
central-isogeny family pullback. It introduces no new assertion attributed to an
external source. The definition `centralIsogenyCentralizerMap` constructs an actual
morphism of the supplied algebraic centralizers; the final results transport the
full centralizer compatibility predicate already defined in
`KPCentralizerCompatibility`.

## Data and scope

The universe `u` is arbitrary. For the centralizer map, let `F` be a field and
supply a commuting square

`i ≫ q = groupHom t ≫ j`,

with `i : S → C`, `j : T → G`, and an isogeny `t : S → T` between the acting
commutative group schemes. Supply `CS : CentralizerDatum i` and
`CT : CentralizerDatum j`. These are the existing data packages: actual represented
closed centralizers, their acting-torus factorizations, and bijective character
restriction/evaluation maps. The construction does not establish existence of
these packages. At this stage `q` can be any ambient group homomorphism, and no
local-field, affine, or splitness hypothesis is needed.

Translation comparisons additionally use the existing nonarchimedean local-field
instances on `F`. Family pullback uses a central isogeny `q`, splitness of `S` and
`T`, and affine and locally finite type ambient groups, exactly as required by
`RootFunctionFamily.centralIsogenyPullback`. The final apartment result uses
monomorphic acting-torus inclusions and apartment data for `localFieldOrder F`.

## Restricting the ambient homomorphism

`TorusCoverTransport.map_mem_torusCentralizer` works over any base scheme with a
flat surjective acting-group map. For a source centralizer point on any test
scheme `U`, it tests commutation with the universal target torus point on
`U × T`. The map `U × S → U × T` is flat and surjective by base change, hence an
epimorphism of schemes and of the over category. Pulling back the desired
commutation identity reduces it to the source centralization identity, followed
by `q`. The given square identifies the two acting-torus maps. Cancellation of
this epimorphism proves target centralization. This uses the full all-test
centralizer, rather than only commutation of rational points.

`range_centralizer_comp_le` applies this result to the actual represented source
centralizer and the flat surjective part of the isogeny hypothesis.
`centralIsogenyCentralizerMap` then factors `CS.j ≫ q` through the representing
monomorphism `CT.j`. Its two comparison lemmas prove

`centralIsogenyCentralizerMap … ≫ CT.j = CS.j ≫ q`

and

`CS.s ≫ centralIsogenyCentralizerMap … = groupHom t ≫ CT.s`.

The second identity follows by cancellation of `CT.j` and the two supplied torus
factorizations. Representability makes this factorization unique. No surjectivity
on centralizer rational points is required.

## Translation naturality

`cocharacterMapReal_centralizerTranslation` is a general comparison for any
commuting torus-centralizer square with bijective restriction/evaluation maps.
It proves equality of the actual real cocharacter vectors by applying the
injective target restriction/evaluation map and evaluating at every target
rational character. Real cocharacter evaluation commutes with `t`; restriction
of the character along the centralizer map commutes with the two torus
factorizations. Finally,
`rationalCharacterValuation_characterRestrict` identifies the scalar valuations.
The negative sign in the existing definition of `centralizerTranslation` is
preserved on both sides.

`centralIsogenyCentralizerMap_translation` specializes this calculation to the
constructed actual centralizer map. It identifies `cocharacterMapReal t` of the
source translation with the target translation of the mapped centralizer point,
before taking any reduced-apartment quotient.

## Full V6 and the whole apartment class

`IsCentralizerCompatible.centralIsogenyPullback` treats every source relative root,
every source centralizer rational point, and every point of that source root
group. The actual relative-root pullback equivalence supplies the corresponding
target root. Conjugation by the source centralizer preserves the source root
group: this follows by applying the existing root-subgroup functoriality to the
inner automorphism and its centralizing identity. Thus both family evaluations
can use `centralIsogenyPullback_apply_root`.

The ambient square for the constructed centralizer map identifies the image of
the conjugate with the conjugate of the image. Translation naturality and
`eval_cocharacterMapReal` identify the V6 correction term. Target full V6 now
proves source full V6, with the existing `WithTop ℝ` convention unchanged. This
argument requires no surjectivity on centralizer points and makes no use of
ambient rational-point injectivity or surjectivity.

`KPApartmentData.IsOmegaCompatible.centralIsogenyPullback` applies the family
result to each member of the image carrier defining the actual pulled-back
apartment. It therefore proves full omega-compatibility of that whole class for
the supplied actual source centralizer. It does not supply V7, AS5, a canonical
class comparison, or the final normalizer-image theorem. Those conclusions are
separate obligations in the surrounding construction.
