# Actual quasi-isomorphism extension to full recognition atlases

This derived construction extends a coherent strong quasi-isomorphism to the
full recognition atlases on exactly the same ambient topological spaces.
It constructs the bounded pullback on every admissible chart pair and proves
its full-domain universal property. Neither original atlas needs to contain
all its local full domains.

The source context is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Definitions 1.2.7 and 1.2.9, printed pages 18–19 (PDF pages
15–16), Proposition 1.2.13(ii), printed page 21 (PDF page 18), and Proposition
1.2.15, printed pages 21–22 (PDF pages 18–19). Strong morphisms retain bounded
algebra maps and their restriction compatibility; quasi-isomorphisms additionally
have an ambient homeomorphism and full relative domain presentations. The
recognized-atlas extension in Proposition 1.2.13(ii) has canonical bounded
restrictions. This module combines the already constructed recognized images
and those restrictions. It is an internal derived extension in this framework,
not a transcription of the unrestricted morphism assertion of Proposition
1.2.15 or the entire maximal-atlas assertion.

The inputs are actual affinoid atlas presentations `A` and `B` over a complete
ultrametric normed field `K`, a strong map `f : StrongHom A B`, its
quasi-isomorphism property `hf`, and intrinsic original-pullback coherence `hc`.
Field, ambient and original index universes are independent, with the two
presentations using the same respective universes. The given coherence relates
original pullbacks with actual local full-domain representations; it does not
supply any recognized image, comparison algebra or extension map. Those objects
are constructed by the imported modules.

`fullRecognitionPresentation` has literal ambient space `A.space` and atlas
`A.atlas.fullRecognitionAtlas`. Its indices are the recognized subsets of
`A.atlas.saturatedAtlas`, with their actual presented affinoid algebras and
charts. The resulting index universe is the ambient universe. The theorem
`fullRecognitionPresentation_hasAllLocalDomains` applies the published
`fullRecognitionAtlas_localDomainFamily` to prove closure of this constructed
atlas. It adds no closure assumption on `A`.

Write `F(V) = hf.recognizedImage hc V` and
`e_V = hf.recognizedImageEquiv hc V`. The earlier constructed image has
literal locus `f.baseMap '' V.locus`, and `e_V` is a bounded algebra equivalence
from `V.algebra` to `F(V).algebra`. Its full restriction naturality is proved in
`QuasiIsoRecognizedNaturality`. The present module imports these results
unchanged, including their construction from actual finite full-domain covers.

For every admissible pair `V`, `W`, the supplied containment is
`f.baseMap '' V.locus ⊆ W.locus`. Thus `F(V)` is literally contained in `W`;
`recognizedImage_subset_of_image_subset` records this fact.
`fullRecognitionPullback` defines the entire bounded algebra map

```text
p(V,W) = e_V.symm composed with F(V).restriction W :
  W.algebra → V.algebra.
```

No chart or inverse map is chosen as an additional premise.
`fullRecognitionPullback_chart` proves the ambient equation

```text
W.chart (comap p(V,W) x) = f.baseMap (V.chart x).
```

The proof identifies comap of the composite with target restriction comap
followed by the inverse equivalence on spectra. The recognized restriction
chart equation, the existing image chart equation and the actual inverse
homeomorphism identity give the result.

`fullRecognitionPullback_naturality` proves the entire bounded map identity
for `U ⊆ V`, `W ⊆ Z`, and admissible pairs `(U,W)` and `(V,Z)`:

```text
U.restriction V composed with p(V,Z)
  = p(U,W) composed with W.restriction Z.
```

Apply the injective bounded algebra equivalence `e_U` to arbitrary algebra
elements. The previously proved forward naturality moves the source
restriction through `e_U` and `e_V`. The two inverse identities cancel those
equivalences. The two canonical target restriction composition identities
then identify both maps. This proves equality on all algebra elements; no
algebra-map equality is inferred from equality on spectra.

`fullRecognitionPullback_represents` proves

```text
Represents K p(V,W) (W.chart ⁻¹' (f.baseMap '' V.locus)).
```

The canonical recognized restriction fully represents `F(V)` inside `W`.
The published `Represents.postcomp_equiv` transports this universal property
through `e_V.symm`, and the literal image-locus equation identifies the
relative subset. Thus the assertion retains all bounded maps from presented
affinoid coefficient tests, rather than only a spectrum image equation.

`fullRecognitionExtension` bundles these maps into an actual strong map from
`A.fullRecognitionPresentation` to `B.fullRecognitionPresentation`. Its ambient
map is exactly `f.baseMap`. For each source chart, `F(V)` supplies a target
chart containing its image. The three proved identities provide chart
compatibility and all admissible source and target restriction compatibility.
The chart ranges are the literal recognized loci. The theorem
`fullRecognitionExtension_baseMap` states the unchanged ambient map.

`fullRecognitionExtension_isQuasiIso` combines the original ambient
homeomorphism with the just proved full representation theorem on every
admissible pair. `fullRecognitionExtension_hasCoherentPullbacks` uses closure
of the constructed source full atlas and the published automatic coherence
theorem. There is no additional premise on either original presentation.

The construction preserves actual nonreduced algebra information, trivial
valuations, general positive polyradii and empty spaces or finite families.
No global Hausdorffness or directedness assumption is introduced. Equivalence
of the original recognized categories without target closure still requires
transport through the separately constructed recognition-idempotence
comparisons; their iterated saturation levels are not identified here.
Arbitrary equivalent-net invariance, maximal-atlas uniqueness, unrestricted
analytic morphism identification, analytic and equivariant sites and Harris
specializations remain obligations of the broader task.
