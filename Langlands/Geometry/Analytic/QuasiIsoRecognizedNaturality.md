# Full bounded naturality of recognized images under coherent quasi-isomorphisms

This derived construction identifies the actual affinoid diagrams associated
with recognized images under a coherent strong quasi-isomorphism. It proves
naturality for the original forward realization comparisons on entire bounded
algebras. It also constructs a natural reverse algebra comparison when the
target contains all local full domains.

The original context is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Proposition 1.2.13(ii) and Proposition 1.2.15, printed pages
21–22 (PDF pages 18–19). The former constructs the canonical bounded restrictions
of the extended recognized atlas; the latter describes compatible affinoid
morphisms and its isomorphism criterion. The present module supplies a derived
comparison for the explicit coherent strong-map scope below. It does not claim
the unrestricted analytic morphism description or maximal-atlas theorem.

The inputs are actual affinoid atlas presentations `A` and `B`, over a complete
ultrametric normed field `K`, a strong map `f : StrongHom A B`, its
quasi-isomorphism property `hf`, and intrinsic original-pullback coherence `hc`.
The field, ambient-space and index universes are independent, with the two
presentations in the same respective universes. In particular, the ambient map
is an actual homeomorphism. The inputs do not supply any recognized comparison
or algebra naturality. The forward results require no source or target
full-domain closure. The reverse results additionally use
`hb : B.atlas.HasAllLocalDomains`, the existing literal closure property.

Write `S(s) = hf.saturatedImageIndex s` and `e_s = hf.saturatedImageEquiv s` for
the constructed image of each source saturated chart and its actual bounded
algebra equivalence. The prior module `QuasiIsoRecognizedImage` supplies these
objects and full saturated restriction naturality. For a source recognized
subset `V`, it also supplies an actual finite realization `c_V`, on unchanged
`V.algebra`, with ambient chart `f.baseMap` composed with `V.chart`, and a
bounded equivalence

```text
alpha_V = hf.recognizedImageEquiv hc V :
  V.algebra ≃ (hf.recognizedImage hc V).algebra.
```

Here and below the algebra equivalences are bounded in both directions.
The module `QuasiIsoReverseRecognition` supplies the forward recognized functor
`F`, and, under target closure, the reverse functor `G` and actual unit and
counit. Its independent construction of these objects is reused unchanged.

`recognitionImageChartDomain_comp_restriction` proves that every canonical
transported chart-domain map commutes with source recognized restriction.
For `U.locus ⊆ V.locus`, it composes `e_s` with the existing entire-algebra
identity for `U.originalRestriction`. `saturatedImage_subset_recognizedImage`
provides the actual image-chart containment needed by subsequent restrictions.

`recognitionImage_originalRestriction` recovers the complete section map to
every chart `S(s)` whose source chart is contained in `V`:

```text
d.originalRestriction S(s) composed with c_V.restrictFromParent
  = e_s composed with V.originalRestriction s,
```

where `d = hf.recognitionImageGluing V`. The Hausdorff instance on `d.locus`
comes from the constructed realization. To prove the identity, take the actual
finite source cover subordinate to the witnessed recognition cover of `V`
and to `s`. Its members lie in both `s` and a defining source component.
Apply `e_s.symm` to separate the two values in the unchanged source chart
algebra, separate them over this full-domain cover, and apply each subordinate
`e_k`. The full saturated naturality equation and the actual bounded inverse
identities convert these tests to target restrictions. The finite section
restriction formula expresses each test through a defining target projection.
The realization projection equation and its full chart-domain naturality then
identify the tests. This proves equality on every algebra element; no equality
of algebra maps is inferred from their spectra.

`recognizedImageEquiv_originalRestriction` applies the existing general
finite-realization comparison theorem to obtain

```text
F(V).originalRestriction S(s) composed with alpha_V
  = e_s composed with V.originalRestriction s.
```

The realization and `F(V)` have definitionally the same literal locus. This
step compares the actual recognized section algebra, including its potentially
different chosen recognition witness, with the original unchanged parent.

`recognizedImageEquiv_naturality` proves the final full bounded identity
for every source recognized containment:

```text
alpha_U composed with U.restriction V
  = F(U).restriction F(V) composed with alpha_V.
```

Its proof applies `alpha_U.symm` and then separates algebra elements over the
actual full-domain cover of `c_U`, whose parent is unchanged `U.algebra`.
On each defining source component, restriction recovery evaluated at
`alpha_U.symm` identifies the test with a canonical restriction of `F(U)`.
The source chart-domain compatibility, restriction recovery for `V`, and the
target recognized restriction identity prove equality of those tests.
`recognizedImageFunctor_naturality` gives the same equation for an arbitrary
arrow in the actual recognized inclusion category.

The bounded forward maps and their actual inverses define
`recognizedImageAffinoidIso`. Applying the proved full naturality gives
`recognizedImageAffinoidNatIso`:

```text
F composed with D_B ≅ D_A,
```

where `D_A` and `D_B` are the existing actual affinoid functors of the saturated
recognized categories, valued in the opposite category of presented affinoid
algebras. Its component hom is the opposite of `alpha_V`. The inverse identities
are the bounded equivalence identities on all algebra elements.
`recognizedImageAffinoidNatIso_over_ambient` proves that its actual spectrum
map satisfies

```text
f.baseMap (V.chart (alpha_V.spectrumHomeomorph x)) = F(V).chart x.
```

For the remaining constructions, target full-domain closure stays explicit.
`reverseRecognizedImageAffinoidNatIso` is the composite

```text
G composed with D_A
  ≅ G composed with (F composed with D_B)
  ≅ (G composed with F) composed with D_B
  ≅ identity composed with D_B
  ≅ D_B.
```

It uses the whiskered inverse forward comparison, the inverse associator, the
actual target counit whiskered with `D_B`, and the left unitor. All these maps
are in the category of actual presented affinoid algebras and bounded maps.

`reverseRecognizedImageNaturalEquiv` extracts the two bounded inverse maps
from each component of this reverse natural isomorphism. If `epsilon_W` is the
actual target counit `F(G(W)) ≅ W`, its forward algebra map is

```text
beta_W = alpha_G(W).symm composed with epsilon_W.hom.restriction,
```

and its inverse is `epsilon_W.inv.restriction` composed with `alpha_G(W)`.
Applying unop to the categorical inverse equations proves the two algebra
inverse identities. Applying unop to naturality proves
`reverseRecognizedImageNaturalEquiv_naturality`, an equality of entire bounded
restriction maps. This is a new natural reverse comparison. No identity with
`reverseRecognizedImageEquiv`, the separately chosen reverse realization
comparison from the earlier module, is asserted.

The actual counit chart equation followed by the forward chart equation proves
`reverseRecognizedImageAffinoidNatIso_over_ambient`. The bounded inverse identity
cancels the intervening forward spectrum homeomorphism. The final theorem
`reverseRecognizedImageNaturalEquiv_chart` states the equivalent inverse-ambient
formula

```text
G(W).chart x = hf.inverseBaseMap (W.chart (beta_W.spectrumHomeomorph x)).
```

These constructions retain nonreduced algebra information, trivial valuations,
general positive polyradii and empty spaces or finite families. They add no
global Hausdorffness or directedness premise. Removing target closure for
arbitrary original presentations still requires comparison of the additional
saturation levels; those categories are not identified definitionally here.
Arbitrary equivalent-net invariance, maximal-atlas uniqueness, the unrestricted
analytic morphism description, analytic and equivariant sites, and Harris
specializations remain separate obligations of the broader task.
