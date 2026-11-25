# Two-out-of-six for full strong quasi-isomorphisms

This module derives left cancellation and two-out-of-six for the
existing full strong quasi-isomorphism class, with independent field,
space and original chart-index universes `u, v, w`. The coefficient field
is complete and ultrametric; there is no separation hypothesis.

## Affinoid-test cancellation

`Represents.of_comp_of_comp` considers bounded maps `a : S → T`,
`b : R → S`, `c : U → R` between presented affinoid algebras. If both
`a.comp b` and `b.comp c` represent full domains, then `a` represents the
inverse image under the spectrum map of `b` of the first represented
locus. The second represented domain has an injective spectrum map, so
the spectrum map of `b` is injective too. This gives the required exact
spectrum range; closedness follows by continuous inverse image.

The second full-domain universal property also makes `b` cancel bounded
maps to every presented test algebra: precompose with `c` and cancel the
represented composite. To factor a test through `a`, first compose it
with `b`, apply the first represented composite's universal property,
and cancel `b`. The same universal property proves uniqueness. All these
are complete bounded-map arguments.

## Source cancellation

`StrongHom.IsQuasiIso.of_saturatedComp_left` handles maps between
constructed saturations. Suppose `f` and `f ≫ g` are full
quasi-isomorphisms. For each recognized subset `W` of the middle space,
choose its constructed recognized preimage `V` under `f`. Its image is
exactly `W`, so `f`'s actual pair map is a bounded equivalence. The
composite's recognized image `Z` of `V` has locus `g(W)`, and its actual
pair map is also a bounded equivalence. Composing with the inverse of the
first comparison gives a bounded equivalence whose whole forward map is
`g`'s actual pair-system map. The ambient map of `g` is a homeomorphism by
cancellation of the two known homeomorphisms. The existing full-recognition
isomorphism criterion now proves that `g` is a full quasi-isomorphism.

`SaturatedAtlasPresentation.isQuasiIso_of_comp_left` reduces arbitrary
saturated strong maps to that result using the actual saturation functor,
then reflects the condition through the compatible original restriction.

## Two-out-of-six

`isQuasiIso_twoOutOfSix` assumes that `f ≫ g` and `g ≫ h` are full
quasi-isomorphisms and proves the same for all three factors. The first
composite makes `g` surjective; the second makes it injective. The
continuous formula `f ∘ (g ∘ f)⁻¹` constructs its inverse homeomorphism,
and hence the homeomorphism underlying `f`.

For each admissible pullback of `f`, choose one containing chart for `g`
and one for `h`. The two known composite quasi-isomorphisms represent
full domains on these chains. The affinoid cancellation lemma applies to
the three actual bounded maps. Injectivity of the ambient map of `g`
identifies its inverse-image locus with `f`'s original chart image. Thus
`f` is a full quasi-isomorphism. Applying the proved source cancellation
twice gives the same conclusion for `g` and `h`.

The module uses existing represented-domain injectivity and uniqueness,
actual recognized images, bounded equivalences, and the full-recognition
isomorphism criterion. It invokes no unproved geometric statement or
external theorem translation.
