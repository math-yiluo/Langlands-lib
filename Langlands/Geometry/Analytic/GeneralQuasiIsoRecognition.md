# Recognized category equivalence without original target closure

Author: Worker 36.

This derived construction retains the original forward recognized-image
functor of a coherent strong quasi-isomorphism and constructs its inverse on
the original recognized categories. It also constructs a reverse natural
isomorphism of the actual presented-affinoid diagrams, including the entire
bounded restrictions. Neither original atlas needs full-domain closure.

## Source and provenance

The original context is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definitions 1.2.7 and 1.2.9, printed pp.18–19 /
PDF pp.15–16, and Propositions 1.2.13(ii)–(iii) and 1.2.15, printed pp.21–22 /
PDF pp.18–19. Registered source: `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original pages were read; no source-specific errata file was found in
the supplied project and Library notes.

The definitions specify the strong-map data and quasi-isomorphism property.
Proposition 1.2.13 constructs the canonical bounded restrictions of the
recognized atlas and its idempotence. Proposition 1.2.15 describes general
analytic morphisms and an isomorphism criterion. This module gives a derived
categorical comparison for the explicit coherent strong-map scope below.
It reuses the constructed full-recognition extension, its proved closure
and coherence, and the constructed iteration and idempotence comparisons.
The reverse objects, equivalence and natural isomorphism are outputs of
these constructions, rather than extra input assumptions. The unrestricted
morphism correspondence is a further obligation.

## Inputs and original forward functor

Let `K` be a complete ultrametric normed field, let `A` and `B` be actual
affinoid atlas presentations, and let `f : StrongHom A B`. The inputs are
`hf : f.IsQuasiIso` and `hc : f.HasCoherentPullbacks`. The latter is the
intrinsic compatibility law on the original bounded pullbacks after every
presented-affinoid coefficient test. It does not supply recognized images
or their algebra comparisons. Field, ambient-space and original-index
universes are independent, with `A` and `B` in the same respective levels.

Write `C_A = A.atlas.saturatedAtlas.RecognizedSubset` and similarly `C_B`.
These are the actual recognized inclusion categories, with canonical
bounded restriction maps. The forward functor remains exactly

```text
F = hf.recognizedImageFunctor hc : C_A → C_B.
```

The earlier construction supplies `F(V).locus = f.baseMap '' V.locus`,
a bounded algebra equivalence `alpha_V : V.algebra ≃ F(V).algebra`, and
its full restriction naturality. No original atlas closure premise is
introduced here.

## Constructed reverse on the original categories

The full-recognition presentations `A*` and `B*` retain the respective
ambient spaces and use the constructed full-recognition atlases. The
previous module constructs the actual strong extension `f*`, proves it is
a quasi-isomorphism, and derives its intrinsic coherence. Both constructed
atlases contain every local full domain.

For `W : C_B`, `B.atlas.fullRecognitionIterationIndex W` constructs its
index in the recognized category of `B*`. Its literal locus is `W.locus`.
The existing reverse-recognition construction can therefore be applied to
`f*`, using the proved closure of `B*`. Its output is an iterated recognized
object over `A`. `A.atlas.fullRecognitionIdempotenceIndex` flattens this
object to an object of `C_A`, constructing its recognition conditions and
preserving its literal locus.

`generalReverseRecognizedImage W` is exactly this composite. Its locus
formula, `generalReverseRecognizedImage_locus`, is

```text
G(W).locus = f.baseMap ⁻¹' W.locus.
```

The proof applies the reverse locus theorem to the extended
quasi-isomorphism and then applies preimage to the proved iteration locus
identity. The ambient map of the extension is the original `f.baseMap`.
The argument uses the actual iteration and idempotence constructions;
these presentation levels are not identified definitionally.

`generalReverseRecognizedImageFunctor` maps an inclusion by monotonicity
of preimage, through these locus identities. Its arrows are actual
recognized inclusions with their canonical full bounded restrictions.

## Unit, counit and equivalence

`generalReverseRecognizedImage_forward_locus` and
`generalForwardRecognizedImage_reverse_locus` prove literal-locus recovery
in the two round trips. They use respectively the injectivity and
surjectivity of the original ambient homeomorphism.

`generalRecognizedImageUnitComponent` constructs `V ≅ G(F(V))` from the
two directions of the first locus equality.
`generalRecognizedImageCounitComponent` similarly constructs `F(G(W)) ≅ W`.
Their inverse laws use uniqueness of inclusion arrows. The same uniqueness
proves naturality of `generalRecognizedImageUnitIso` and
`generalRecognizedImageCounitIso`, and the triangle law of
`generalRecognizedImageEquivalence : C_A ≌ C_B`.

`generalRecognizedAffinoidFamily_image` proves the literal-family equality

```text
(fun S => f.baseMap '' S) '' A.atlas.recognizedAffinoidFamily
  = B.atlas.recognizedAffinoidFamily.
```

The forward inclusion uses the original constructed recognized image.
The reverse inclusion uses `G(W)` and surjectivity of the homeomorphism.
The algebra comparisons that strengthen this category and family
comparison are constructed next.

## Actual affinoid diagrams and full bounded naturality

Let `D_A` and `D_B` be the existing `RecognizedSubset.toAffinoidSpace`
functors. They take values in the opposite category of actual presented
affinoid algebras and bounded algebra maps. The original forward comparison
is `F ⋙ D_B ≅ D_A`.

`generalReverseRecognizedImageAffinoidNatIso` constructs

```text
G ⋙ D_A ≅ D_B
```

by whiskering the inverse forward comparison with `G`, applying the inverse
associator, whiskering the constructed counit `G ⋙ F ≅ identity` with
`D_B`, and applying the left unitor. Thus the comparison identifies actual
bounded maps, including algebra information invisible on spectrum points.

`generalReverseRecognizedImageNaturalEquiv W` extracts the two bounded
inverse algebra maps from this natural isomorphism. If `epsilon_W` is the
constructed counit, its forward map has direction
`W.algebra → G(W).algebra` and is

```text
beta_W = alpha_G(W).symm composed with epsilon_W.hom.restriction.
```

Its inverse is `epsilon_W.inv.restriction` composed with `alpha_G(W)`.
Applying unop to the categorical inverse identities and evaluating at each
algebra element proves both inverse laws. No agreement with a separately
chosen reverse realization comparison from the target-closed construction
is asserted.

For every inclusion `p : U → V`,
`generalReverseRecognizedImageNaturalEquiv_naturality` proves

```text
beta_U composed with p.restriction
  = (G.map p).restriction composed with beta_V.
```

The proof applies unop to naturality of the actual affinoid natural
isomorphism. It is equality of entire bounded algebra maps.

## Spectrum comparison and scope

`generalReverseRecognizedImageAffinoidNatIso_over_ambient` states that the
hom component's actual spectrum map `sigma_W` satisfies

```text
W.chart (sigma_W x) = f.baseMap (G(W).chart x).
```

The implemented proof uses the actual counit's chart equation, the forward
recognized-image chart equation, and cancellation by the bounded algebra
equivalence's spectrum homeomorphism. The final
`generalReverseRecognizedImageNaturalEquiv_chart` applies the original
ambient homeomorphism's injectivity to prove the equivalent inverse formula

```text
G(W).chart x = hf.inverseBaseMap (W.chart (beta_W.spectrumHomeomorph x)).
```

The original coherence law remains explicit. There is no original source
or target full-domain closure premise, no global Hausdorffness or
directedness premise, and no nontrivial valuation, reducedness, nonzero
algebra or nonempty-family assumption. This unit extends the earlier
reverse comparison by removing its original target-closure premise.
Arbitrary equivalent-net invariance, maximal-atlas uniqueness, unrestricted
analytic morphism identification, analytic and equivariant etale and
quasi-etale sites, compact and distinguished domains, and Harris
specializations remain further work of the broader task.
