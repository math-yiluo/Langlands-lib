# Invertibility of the canonical presheaf pullback tensor comparison

The theorem
`Langlands.Scheme.Modules.presheafPullbackTensorComparisonIsIso` has exactly
the published type
`Langlands.Scheme.Modules.presheafPullbackTensorComparisonIsIsoStatement.{u}`.
It proves that, for every morphism `f : X ⟶ Y` of schemes in arbitrary
universe `u`, the fixed natural transformation
`presheafPullbackTensorComparison f` is an isomorphism. There are no
additional hypotheses or parameters.

Write `L = presheafPullback f` and
`A(V) = (PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj V)`.
The component in question is the published
`presheafPullbackTensorComparisonApp f M N`, from `L.obj (M ⊗ N)` to
`L.obj M ⊗ L.obj N`. The proof keeps this component throughout its
extension argument. Its source, target, ring-presheaf map and inverse-image
opens functor are those of the imported construction.

## Extension from free Yoneda generators

The private lemma `isIso_app_of_freeYoneda` applies to a natural
transformation `α : F ⟶ G` between functors out of presheaves of modules
over a small category, where both functors preserve colimits of size
`(u,u)`. If `α` is invertible on every free Yoneda generator, the lemma
proves it invertible at every presheaf of modules `M`.

For any presheaf `N`, Mathlib's `N.freeYonedaCoproduct` is the coproduct of
the free Yoneda generators indexed by pairs consisting of an object and
a section of `N` over it, with this type used as a discrete category. The assumed isomorphisms make the
transformation whiskered with this diagram a natural isomorphism.
`CategoryTheory.Limits.isIso_app_coconePt_of_preservesColimit` then proves
invertibility at this coproduct. Apply this argument to any `N`.

Next use Mathlib's canonical cokernel presentation of `M` by such
coproducts. Its diagram is `parallelPair M.toFreeYonedaCoproduct 0`, and
its colimit cocone is `M.freeYonedaCoproductsCokernelCofork`, certified by
`M.isColimitFreeYonedaCoproductsCokernelCofork`. Both objects of this
diagram are coproducts already covered by the preceding argument. The
same preserved-colimit lemma therefore proves invertibility at `M`.
For the finite diagram, preservation of colimits at universe zero is
obtained explicitly by `preservesSmallestColimits_of_preservesColimits`.

## Application in both tensor variables

The private lemma `comparison_isIso_of_freeYoneda` takes invertibility of
the exact comparison at every pair `A(V), A(W)` and extends it to all
module presheaves. First fix `M = A(V)` and consider the natural
transformation

```
tensorLeft M ⋙ L ⟶ L ⋙ tensorLeft (L.obj M).
```

Its component at `N` is the published comparison. Its naturality follows
from `presheafPullbackTensorComparisonApp_naturality`, with the first
morphism specialized to the identity. The preceding extension lemma
proves this component invertible for every `N`.

Then fix an arbitrary `N` and use the transformation

```
tensorRight N ⋙ L ⟶ L ⋙ tensorRight (L.obj N).
```

Its naturality uses the same published theorem, now with the second
morphism the identity. The first extension supplies its generator
components, and a second application gives invertibility for every `M`.
`CategoryTheory.NatIso.isIso_of_isIso_app` assembles these componentwise
results into invertibility of `presheafPullbackTensorComparison f`.

All four tensor functors preserve the needed colimits by Mathlib's
instances for `PresheafOfModulesOfCommRing`. The local monoidal instance
is precisely that existing sectionwise tensor structure. Pullback
preserves colimits because `presheafPullbackPushforwardAdjunction f`
makes it a left adjoint. Thus preservation assumptions of the private
general lemma are discharged by the imported constructions.

The public theorem discharges the remaining generator-pair hypothesis
using `presheafPullbackTensorComparisonFreeYonedaIso f V W`. Its
published hom law
`presheafPullbackTensorComparisonFreeYonedaIso_hom` rewrites the desired
component to the hom of this isomorphism, which is invertible. This exact
hom equality ensures that the theorem concerns the specified canonical
comparison.

## Internal provenance

This is an internal derived proof using the pinned Mathlib free-Yoneda
coproduct and cokernel presentations, preservation-of-colimit APIs, and
the imported Library generator-pair isomorphism. That isomorphism combines
the pullback formula for a single free Yoneda generator with the
intersection tensor calculation and preservation of intersections by
inverse image; its hom law checks compatibility with the original
adjunction-defined comparison. The present module supplies the extension
from generator pairs to arbitrary module presheaves.

No external theorem is transcribed. In particular, the motivating Stacks
sheaf result cited in the statement's companion is not used as a proof of
this presheaf proposition. The argument uses neither the final sheaf
pullback tensor theorem nor a monoidal pullback structure. No flatness,
affineness, quasicoherence, local freeness or sheafness condition is
introduced, and no invertibility of the desired comparison is assumed.
Worker 441 implemented the colimit extension and this final assembly;
the generator constructions are imported by their published Lean names.
