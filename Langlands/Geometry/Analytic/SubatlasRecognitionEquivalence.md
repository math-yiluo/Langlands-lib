# Recognized category invariance under locally refining selection

This internal construction compares the recognized affinoid inclusion
categories of an original atlas and a locally refining selected subatlas. Both
directions preserve literal ambient loci. The actual presented-affinoid
diagrams are naturally isomorphic in both directions through bounded algebra
maps.

The source context is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), the special-cover and recognition definitions on printed
pages 20–21 (PDF pages 17–18) and Proposition 1.2.13(ii) on printed page 21.
This is derived infrastructure for the atlas-independence construction.

Let `a` be an indexed affinoid atlas over a complete ultrametric normed field
`K`, let `P` be a locally refining selection, and put `b = a.subatlas P hP`.
The ambient and original index universes are independent. The categories in
the conclusion are those of intrinsically recognized subsets of
`a.saturatedAtlas` and `b.saturatedAtlas`. Their arrows are literal ambient
inclusions; their algebra restrictions are the bounded maps constructed
through canonical special-subset section algebras.

The existing forward functor `F = subatlasRecognitionFunctor` recognizes an
arbitrary original recognized subset with respect to the selected atlas.
`subatlasReverseRecognitionFunctor`, denoted `G`, uses the independently
constructed reverse recognition of `SubatlasReverseRecognition`.
Theorem `subatlasReverseRecognitionFunctor_locus` proves that its object
has the unchanged literal locus. Its action on arrows uses this equality
to transport each containment, and functor laws follow from uniqueness of
the recognized inclusion arrows.

The original round trip `G(F(V))` and the selected round trip `F(G(W))`
have the original literal loci. `subatlasRecognitionUnitComponent` and
`subatlasRecognitionCounitComponent` therefore construct actual recognized
inclusions in both directions. The category is thin, so both inverse laws,
naturality and the equivalence triangle identity follow from inclusion
uniqueness. Their images in the actual affinoid diagram are mutually inverse
bounded maps, because the recognized restriction construction already proves
its identity and composition laws.

`subatlasRecognitionEquivalence` packages these functors, unit and counit
as an equivalence

```text
a.saturatedAtlas.RecognizedSubset ≌
  b.saturatedAtlas.RecognizedSubset.
```

Theorem `subatlas_recognizedAffinoidFamily` also proves equality of the
literal families of subsets of the fixed ambient space. The two directions
use the constructed forward and reverse objects with their proved locus
equalities. No equivalence or recognized output is supplied as an input.

Write `A` and `B` for the actual presented-affinoid functors from the original
and selected recognized categories. The previously constructed forward
comparison is `α : F ⋙ B ≅ A`. The new reverse comparison is the composition

```text
G ⋙ A  ≅  G ⋙ F ⋙ B  ≅  (G ⋙ F) ⋙ B  ≅  B,
```

using `α.symm` on every object of `G`, the associativity isomorphism, and
the actual selected counit. It is implemented by
`subatlasReverseRecognitionAffinoidNatIso`. All of its maps are actual
bounded algebra maps in the opposite category; naturality follows from the
already proved full forward naturality and the canonical recognized
restriction functor. No equality of algebra maps is inferred from equality
of spectrum maps.

`subatlasReverseRecognitionNaturalEquiv` extracts the bounded maps and
their inverse identities from each component of this reverse natural
isomorphism. Its direction on algebras is

```text
W.algebra ≃ (G.obj W).algebra.
```

If `e` is the forward algebra equivalence at `G(W)` and `ε_W : F(G(W)) ≅ W`
is the selected counit, the forward map of this new algebra equivalence is
`e.symm ∘ ε_W.hom.restriction`. Its inverse is
`ε_W.inv.restriction ∘ e`. This is a new natural comparison; the unit does
not assert equality with the separate realization equivalence
`subatlasReverseRecognizedSubsetEquiv`.

For every selected recognized inclusion `f : U ⟶ V`,
`subatlasReverseRecognitionNaturalEquiv_naturality` proves the equality
of entire bounded maps

```text
e_U ∘ f.restriction = (G.map f).restriction ∘ e_V.
```

The proof takes the underlying algebra-map equality from categorical
naturality. The reverse ambient-chart theorem follows by applying
`ε_W.hom.chart_naturality` to the inverse forward spectrum comparison,
then using the forward chart equation and its inverse identity.
`subatlasReverseRecognitionNaturalEquiv_chart` gives the resulting equation
directly for the spectrum homeomorphism of the extracted bounded algebra
equivalence.

Together with the forward comparison this identifies the two actual
recognized affinoid diagrams, including their nonreduced algebra
information, over the same literal ambient subsets. It also gives equality
of the recognized families under locally refining selection. Arbitrary
equivalent-net invariance, maximal-atlas uniqueness, the unrestricted
analytic morphism category, analytic etale and equivariant sites, and the
Harris specialization remain separate obligations. This unit does not claim
completion of Proposition 1.2.13 or of the analytic-foundation task.
