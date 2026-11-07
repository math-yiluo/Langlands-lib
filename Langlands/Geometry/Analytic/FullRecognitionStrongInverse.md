# Actual inverse strong maps on full recognition atlases

Author: Worker 36.

This module constructs an actual isomorphism in the category of saturated
affinoid atlas presentations from a coherent strong quasi-isomorphism of the
original presentations. Its forward map is the previously constructed full
recognition extension. Its inverse has a bounded pullback on every admissible
pair of recognized charts. Both compositions equal the entire strong identity,
including the bounded algebra maps.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original passages were read:

- Definitions 1.2.7 and 1.2.9, printed pp.18–19 / PDF pp.15–16, specify strong
  morphisms and quasi-isomorphisms through actual affinoid charts and domains.
- Proposition 1.2.13(ii)–(iii), printed p.21 / PDF p.18, constructs canonical
  restrictions on recognized affinoid domains and gives recognition idempotence.
- Proposition 1.2.15, printed p.22 / PDF p.19, states the broader analytic
  morphism correspondence and isomorphism criterion.

This is a derived construction using the existing recognized-image diagram
comparison, the constructed reverse diagram comparison and the category of
saturated presentations. It retains the explicit intrinsic pullback coherence
law on the original strong morphism. It does not claim the unrestricted
assertion of Proposition 1.2.15.

## Inputs and full recognition objects

Let `K : Type u` be a complete ultrametric normed field, and let `A` and `B`
be actual affinoid atlas presentations with ambient universe `v` and original
index universe `w`. Let `f : StrongHom A B`, with
`hf : f.IsQuasiIso` and `hc : f.HasCoherentPullbacks`.
The imported definitions retain actual finite presented algebras, their
Banach spectra, the atlas net and full bounded restriction maps.
The coherence premise is a law on the original bounded pullbacks after
presented-affinoid coefficient tests; it supplies no reverse map or recognized
diagram as input.

`SaturatedAtlasPresentation.ofFullRecognition A` packages
`A.fullRecognitionPresentation` with its proved full local-domain closure.
Its ambient space is the original `A.space`; its chart indices are
`A.atlas.saturatedAtlas.RecognizedSubset`, in universe `v`.
Thus its type is `SaturatedAtlasPresentation.{u,v,v} K`.
The same construction applies to `B`. Neither original atlas needs closure
under all local domains.

Write `G(W) = hf.generalReverseRecognizedImage hc W` for the previously
constructed reverse recognized object and

```text
beta_W : W.algebra ≃ G(W).algebra
```

for `generalReverseRecognizedImageNaturalEquiv`. These are bounded algebra
equivalences extracted from an actual natural isomorphism of affinoid diagrams.
The reverse ambient map is the inverse of the original homeomorphism,
`hf.inverseBaseMap`.

## Every reverse bounded pullback

`generalReverseRecognizedImage_locus_eq_inverse_image` proves

```text
G(W).locus = hf.inverseBaseMap '' W.locus.
```

It rewrites the existing preimage formula and uses the two ambient inverse
identities. Consequently every reverse-admissible inclusion
`hf.inverseBaseMap '' W.locus ⊆ V.locus` gives the canonical inclusion
`G(W).locus ⊆ V.locus`.

`fullRecognitionReversePullback` constructs the whole bounded map

```text
q(W,V) : V.algebra → W.algebra
q(W,V) = beta_W.symm ∘ restriction(G(W),V).
```

`fullRecognitionReversePullback_chart` proves, for every spectrum point `x`,

```text
V.chart (comap q(W,V) x) = hf.inverseBaseMap (W.chart x).
```

The proof uses the contravariant spectrum homeomorphism of `beta_W`,
the canonical restriction chart equation, the reverse comparison chart
equation and cancellation of the spectrum homeomorphism.

`fullRecognitionReversePullback_naturality` quantifies over all nested source
charts `U ⊆ W` and target charts `V ⊆ Z`, with the two required admissibility
inclusions, and proves the equality of bounded algebra maps

```text
restriction(U,W) ∘ q(W,Z) = q(U,V) ∘ restriction(V,Z).
```

At each algebra element, injectivity of `beta_U` reduces this to the already
proved whole-map naturality of `beta`, the inverse laws of the two bounded
equivalences and both canonical restriction-composition laws.
No algebra-map equality is inferred from spectrum points.

`fullRecognitionReversePullback_represents` proves the complete relative
affinoid-domain universal property for `q(W,V)` on

```text
V.chart ⁻¹' (hf.inverseBaseMap '' W.locus).
```

It transports the existing canonical restriction representation through
`beta_W.symm` using `Represents.postcomp_equiv`, then rewrites the literal
locus identity. This retains closedness, the exact spectrum image and unique
factorization for every bounded map into every presented-affinoid coefficient
algebra whose spectrum image lies in the domain.

## The actual reverse strong quasi-isomorphism

`fullRecognitionReverse` installs these maps on every admissible pair as an
actual `StrongHom B.fullRecognitionPresentation A.fullRecognitionPresentation`.
For each `W`, its containing target is the constructed `G(W)`.
The two compatibility fields use the complete chart and bounded naturality
identities above, with chart ranges rewritten to the recognized loci.
`fullRecognitionReverse_baseMap` is the definitional identity with
`hf.inverseBaseMap`.

`fullRecognitionReverse_isQuasiIso` combines the inverse ambient
homeomorphism with the full domain representation at every admissible pair.
`fullRecognitionReverse_hasCoherentPullbacks` follows from the proved closure
of the constructed source full recognition atlas.

## Entire strong inverse identities

`fullRecognitionPullback_generalReverse` identifies the forward extension
pullback at `G(W),W` with `beta_W`. This is definitional: the reverse comparison
was constructed from the inverse forward comparison and the actual counit
restriction of the recognized-category equivalence.
`fullRecognitionReversePullback_generalReverse` identifies `q(W,G(W))`
with `beta_W.symm`, since the canonical self-restriction is the identity.
Both equalities concern entire bounded maps.

`fullRecognitionReverse_comp_extension` proves that the reverse followed by
the forward extension is `StrongHom.id B.fullRecognitionPresentation`.
The ambient equality is the original homeomorphism inverse identity.
Saturated-source extensionality reduces full strong-map equality to one
admissible target per source chart. For `W`, choose `W` itself and compute the
composition along `W → G(W) → W` by `saturatedComp_pullback`.
The resulting bounded map is `beta_W.symm ∘ beta_W`, which is the canonical
identity restriction. Extensionality then recovers every other admissible
pullback.

`fullRecognitionExtension_comp_reverse` proves the other entire strong
identity. Postcompose both sides by the forward full quasi-isomorphism,
use associativity and the preceding identity, then apply
`IsQuasiIso.cancel_saturatedComp`. That cancellation uses the full relative
domain uniqueness property and saturated-source extensionality, so it
preserves all bounded algebra information.

`fullRecognitionStrongIso` packages these two maps and identities as

```text
SaturatedAtlasPresentation.ofFullRecognition A ≅
  SaturatedAtlasPresentation.ofFullRecognition B.
```

Its `hom` is precisely `hf.fullRecognitionExtension hc`; its `inv` is
precisely `hf.fullRecognitionReverse hc`. The category uses the previously
constructed saturated strong composition, with all admissible pullbacks.

## Scope

There is no original domain-closure, chart-directedness, chart-cofinality,
global Hausdorffness, nontrivial-valuation, reducedness or nonemptiness premise
in addition to the stated actual atlas, quasi-isomorphism and coherence inputs.
Only the constructed full recognition atlases supply domain closure.
This construction upgrades the recognized-category comparison to an actual
strong isomorphism on full recognition presentations. Arbitrary equivalent-net
invariance, maximal-atlas uniqueness, unrestricted analytic morphism
identification, analytic sites and Harris specializations remain further work.
