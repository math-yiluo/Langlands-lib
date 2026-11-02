# Unconditional localization of full presented affinoid domains

Author: Worker 36.

For every complete ultrametric normed field `K : Type u`, actual
positive-polyradius presented affinoid algebra `A`, and full represented
domain `U : Domain K A`, this module constructs

```text
U.locusHomeomorph : BanachSpectrum U.algebra ≃ₜ U.locus
U.localizationEquivalence : Domain K U.algebra ≌ Over U.
```

No spectral-injectivity hypothesis is supplied. The published theorem
`Domain.spectrumEmbedding` proves that the stored structural spectrum map
of every full domain is a closed embedding. This module uses its injectivity
to specialize the already constructed conditional localization API.
The field, algebra and domain hypotheses are otherwise unchanged; arbitrary
positive radii, trivial valuations, nonreduced and zero quotients, and empty
spectra remain in scope.

## Structural homeomorphism and naturality

`spectrumMap_injective` exposes the injectivity consequence of the published
embedding theorem for the actual structural map. `locusHomeomorph` uses the
existing surjective corestriction `spectrumToLocus`, its proved continuity
and closed-map property, and that injectivity. Its forward function is
exactly `spectrumToLocus`; composing with the subtype inclusion is exactly
`spectrumMap`.

`locusHomeomorph_naturality` retains the spectrum map induced by every actual
bounded restriction. `spectrumToLocusNatIso` bundles these homeomorphisms as
a natural isomorphism from `toTopologicalSpace K A` to `locusFunctor K A`.
Its forward natural transformation is proved equal to the existing
`spectrumToLocusNat K A`.

## Full-domain composition and localization

`Represents.comp` proves full representation for the composite of any two
full representations. It regards the first representation as an actual
`Domain`, obtains its proved spectral injectivity, and applies
`Represents.comp_of_injective`. Thus the represented locus is the image of
the second locus under the first structural spectrum map, and factorization
still tests every presented affinoid algebra.

`U.extend V` retains exactly `V.algebra`, has structural bounded map
`V.baseMap.comp U.baseMap`, and represents `U.spectrumMap '' V.locus`.
The projection equations are definitional. The locus lies inside `U.locus`,
and the structural spectrum map is the composite of the two original
spectrum maps. `extendInclusion` has exactly `V.baseMap` as its bounded
restriction into `U`.

`extendFunctor` retains the entire bounded restrictions between inner
domains. Its full-faithfulness construction is the existing one: full
test-map uniqueness for `U` cancels precomposition with `U.baseMap`.
Its affinoid and topological realization functors are literally unchanged.
`extendOverFunctor` also retains the actual inclusion into `U`; forgetting
that inclusion gives `extendFunctor`.

`localizationEquivalence` specializes
`localizationEquivalenceOfInjective` with the proved injectivity.
Its forward functor is `extendOverFunctor` and its inverse is
`U.relativeFunctor`. The unit and counit are the previously constructed
bounded-identity round-trip comparisons, with their naturality and triangle
identity. The relative object retains the ambient domain's actual algebra
and the given inclusion's bounded restriction as structural map.

`relative_locus_eq_preimage` identifies its locus with the entire inverse
image `U.spectrumMap ⁻¹' V.locus`. The two round-trip locus equations recover
the original subsets. `extendLocusHomeomorph` identifies each inner locus
with its extended subspace by exactly `U.spectrumMap`.

`extendAssocIso` compares `U.extend (V.extend W)` with
`(U.extend V).extend W`. Both bounded maps are the identity on `W.algebra`;
associativity of the actual bounded structural maps proves their base
equations. Restriction extensionality proves the inverse identities. This
is the stated comparison for three nested domains; no additional coherence
theorem is asserted.

## Provenance and scope

This is an internal construction from the published full-domain spectrum
embedding theorem, `DomainEmbeddedLocalization`, `DomainTopology`, and
`DomainRelativeRepresentation`. The new deductions remove the supplied
injectivity premise, identify the actual spectrum corestriction naturally,
and compare repeated extension. The embedding proof's authors are credited
in its imported paired documentation; no private draft is reused here.

The source context of the imported representation property and embedding
theorem is Berkovich's *Non-archimedean analytic spaces* (Trieste lectures,
2009), Definition 2.2.1 on p. 9 and Fact 2.2.3(i) on p. 10, as cited in
their paired Markdown. No additional original-source assertion is used in
this categorical construction.

These results concern existing full represented domains in the Library's
presentation category. They do not construct arbitrary intersections or
base changes, saturate an analytic atlas, extend the algebra sheaf to the
full analytic G-topology, construct analytic etale sites, or supply Harris
towers.
