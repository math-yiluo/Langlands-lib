# Apartment pullback through an actual central isogeny

This derived construction pulls back an entire apartment of actual root-datum
valuations through a supplied central-isogeny square. It constructs an affine
equivalence of the actual valuation-point spaces and proves that their original
normalizer actions commute with that equivalence.

The setup is a field `k` in arbitrary universe `u`, affine locally finite type
group schemes `C` and `G`, split tori `S` and `T`, and monomorphic embeddings
`i : S.toGrp ⟶ C` and `j : T.toGrp ⟶ G`. The supplied maps are a central isogeny
`q : C ⟶ G` and a torus isogeny `t : S ⟶ T`, with
`i ≫ q = CommGroupScheme.groupHom t ≫ j`. A function `ω : kˣ → ℝ` and target
apartment data `D : KPApartmentData j ω` are retained. No property of `ω` beyond
those already expressed by `D` is needed. The scalar-compatibility lemma itself
does not require the monomorphism instances.

## Compatibility with the scalar valuation

`IsSplitTorusCompatible.centralIsogenyPullback` proves V6 for the normalized
family pullback from `CentralIsogenyFunctions`. Given a source root, the actual
root-support equivalence lifts it to a target root. An image of a source
torus point centralizes the source torus; conjugation therefore preserves each
source root group, as follows from the subgroup-functor compatibility with
inner automorphisms.

Evaluation of the pullback on that conjugated point and on the original point
then reduces to target evaluation. The supplied square maps source torus
conjugation to target torus conjugation. Rational character evaluation commutes
with restriction along `t`, so the target V6 equation is precisely the source
equation, with the same `ω` and the same sign convention. This argument uses
actual point maps, not ambient rational-point bijectivity.

## Pullback apartment and its points

`KPApartmentData.centralIsogenyPullback` defines the source carrier to be the
image of `D.carrier` under normalized family pullback. Its orbit witness is the
pullback of a target witness. The complete valuation transfer from
`CentralIsogenyFullValuation` and the V6 lemma above supply the two predicates
required of that witness. Pullback commutes with real-cocharacter translation,
and the real-cocharacter map induced by the torus isogeny is bijective. These
facts identify the image carrier with the entire source translation orbit.

Normalizer stability follows from the proved equivariance of normalized
pullback and the actual map `splitTorusIsogenyNormalizerMap` on normalizer
points. Thus the construction fills every field of `KPApartmentData`; it does
not assume source apartment data as an additional input.

`centralIsogenyApartmentEquiv` sends a target valuation point to its actual
normalized pullback. It is onto by the definition of the image carrier.
It is injective because every point of `D` is a normalized valuation and
normalized pullback is injective on such families. Its value lemma records
this exact underlying point map.

## Affine structure and normalizer actions

`centralIsogenyApartmentEquiv_vadd` proves, for
`v : TranslationSpace i` and `x : D.Apartment`, that pulling back
`centralIsogenyTranslationEquiv ... v +ᵥ x` equals `v` translated onto the
pullback of `x`. The proof passes to a real-cocharacter representative of the
source quotient and applies the family translation identity.

The entry definition `centralIsogenyApartmentAffineEquiv` equips the point
bijection with the inverse of `centralIsogenyTranslationEquiv` as its linear
part. Its domain is `D.Apartment` and its codomain is the apartment of the
constructed source data. Surjectivity of the forward translation equivalence
converts the preceding translation formula into the affine-map law.

For each actual source normalizer point `n`, the theorem
`centralIsogenyApartmentEquiv_smul` intertwines its source action with the
target action of `splitTorusIsogenyNormalizerMap ... n`. The final theorem
`centralIsogenyApartmentAffineEquiv_normalizer` states the corresponding
commuting square of affine equivalences: first acting in the target and then
pulling back equals first pulling back and then acting in the source.

## Provenance and scope

This is an internal derivation from the existing valuation, quotient
translation, normalized-family and actual-normalizer constructions. It adds
no independently attributed assertion from the literature. The source torus,
torus isogeny and commuting square remain supplied inputs. The construction
does not establish the source apartment axioms, the correspondence of affine
root sets, an affine Weyl group comparison, or
`SimplyConnectedNormalizerAffineWeylStatement`. Those remain separate
obligations for the host proof.
