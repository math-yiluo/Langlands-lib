# Natural equivariant bounded atlas comparison for actual affinoid induction

Author: Worker 56.

This module constructs a natural isomorphism between the disjoint coset-family
atlas realization and the atlas on the original balanced quotient. The
comparison retains the existing spectrum homeomorphism, unchanged chart
indices and bounded identity maps on the original affinoid algebras. Its inverse
laws, equivariance and naturality hold for entire bounded atlas morphisms.

The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.

## Inputs and the two constructions

Let `K : Type u` be a complete normed field with ultrametric distance,
`G : Type v` a topological group, and `H : Subgroup G` an open subgroup,
with `hH : IsOpen (H : Set G)`. An input
`X : NormContinuousSpace K H` is an object of the geometric opposite of
the category of norm-continuous actions on actual finite positive-polyradius
affinoid quotient algebras. Write `A_X = X.unop.obj.V`. A geometric arrow
`f : X ⟶ Y` retains the original equivariant bounded map `f* : A_Y → A_X`.

The source construction first applies `functor H` from
[InducedFunctor](InducedFunctor.md), obtaining the full-group action on the
coset family from [InducedAction](InducedAction.md), then applies
`AffinoidFamily.atlasFunctor` to the entire action. Its underlying space is
the sigma family of original spectra. Its chart indices are cosets for
which that spectrum is nonempty, and every chart algebra is `A_X`.

The target is `equivariantAtlasFunctor H hH` from
[InducedEquivariantAtlas](InducedEquivariantAtlas.md). Its underlying space is
`Spectrum H X.unop = G ×_H LocalSpectrum H X.unop` with the original
product-quotient topology. Its atlas was constructed by transporting the
source disjoint atlas along `spectrumHomeomorph H X.unop hH`. Thus its chart
indices and original algebras agree with those of the source. The full-group
action is the actual balanced quotient action with the bounded inverse
subgroup correction maps.

Both constructions take values in
`Action (AffinoidAtlasPresentation.{u, max u v, v} K) G`.
No finite-index, reducedness, radius-one or nonempty-spectrum hypothesis is
added. Empty spectra yield no charts. Neither an output atlas nor a comparison
isomorphism is an input.

## Forward and inverse bounded atlas maps

`atlasComparisonHom H hH X` is a chosen bounded atlas morphism from
`(family H X.unop).atlasPresentation` to `atlasPresentation H hH X`.
Its continuous base map is precisely the existing `spectrumHomeomorph`:

`(c, x) ↦ [c.out, x]`.

Its chart index map is the identity and its pullback on every chart is the
bounded algebra identity of `A_X`. The chart equation follows from the
construction of the transported chart and spectrum pullback by the algebra
identity. Containment between nonempty disjoint source charts forces equality
of their indices. This proves index monotonicity and reduces compatibility
with restrictions to the bounded identity equation.

`atlasComparisonInv H hH X` has the inverse homeomorphism as its base map,
the same identity index map and the same bounded identity pullbacks. Its chart
equation is the inverse-homeomorphism law on the original disjoint chart.
The corresponding uniqueness theorem for transported nonempty disjoint charts
proves index monotonicity and restriction compatibility.

The four projection lemmas `atlasComparisonHom_indexMap`,
`atlasComparisonInv_indexMap`, `atlasComparisonHom_pullback` and
`atlasComparisonInv_pullback` expose these identity data.

`atlasComparisonHom_inv` and `atlasComparisonInv_hom` prove both categorical
inverse laws. The proof compares all nonproof atlas-morphism fields: the
continuous base maps using the two homeomorphism laws, the chart index maps,
and the composed bounded identity pullbacks by equality on the original
algebras. `atlasComparisonIso` packages these maps and laws as an isomorphism
of actual chosen atlas presentations.

## Equivariance and naturality

For every `g : G`, `atlasComparisonHom_equivariant` states

`(actionMap H X.unop g).atlasMap ≫ atlasComparisonHom H hH X =`
`atlasComparisonHom H hH X ≫ atlasActionMap H hH X g`.

The base-map equation is the existing `actionMap_realization`. Both sides
translate the same coset index. Their bounded pullbacks are the same original
inverse correction operator composed with a bounded identity on the relevant
side. Equality follows directly on the original algebra; spectrum-point
separation is not used. This proves the entire bounded atlas equation,
including nilpotent information. Mathlib's `Action.mkIso` then constructs
`equivariantAtlasComparisonIso H hH X`. The inverse is equivariant by its
inverse laws and the proved forward equivariance, without an additional
inverse-equivariance assumption.

For every input arrow `f : X ⟶ Y`, `atlasComparisonHom_naturality` proves

`(familyMap H f).atlasMap ≫ atlasComparisonHom H hH Y =`
`atlasComparisonHom H hH X ≫ atlasMap H hH f`.

On base spaces this is `spectrumHomeomorph_naturality`: both sides send
`(c,x)` to `[c.out, localSpectrumMap H f x]`. Both chosen chart targets retain
the same coset, with target nonemptiness obtained by seminorm pullback. On
chart algebras both sides are `f*` composed with bounded identities. The proof
again compares complete atlas morphisms and proves equality directly on the
original algebras.

`equivariantAtlasComparison` packages the component isomorphisms and this
naturality as

```
functor H ⋙ (AffinoidFamily.atlasFunctor (K := K)).mapAction G ≅
  equivariantAtlasFunctor H hH.
```

The lemmas `equivariantAtlasComparison_hom_baseMap` and
`equivariantAtlasComparison_inv_baseMap` prove by reflexivity that the forward
and inverse continuous base maps of each component are exactly those of
`spectrumComparison H hH`. This identifies the actual topological comparison
retained by the bounded construction, in both directions.

## Provenance and scope

The original motivation is Berkovich's unfinished *Etale equivariant sheaves
on p-adic analytic spaces* (1995–1996), Construction 1.1.2, printed/PDF page 2.
It forms copies indexed by `G/H` and acts between them using the subgroup
element determined by `g*g_i = g_j*h`. The original page was read directly.
The present comparison and its categorical packaging are derived internally
for the already constructed genuine affinoid case; they are not a separate
comparison theorem quoted from the manuscript.

Registered original:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`;
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The construction reuses the actual disjoint family atlas and its transport,
the constructed spectrum homeomorphism and equivariant bounded induction
maps, the category of chosen atlas presentations, and Mathlib's categorical
actions and natural isomorphisms. It assumes none of the output comparison
maps, inverse equations, equivariance or naturality. It preserves arbitrary
positive radii, original quotient algebras and the balanced quotient topology.

The result is a comparison in the concrete category of atlas presentations.
It does not identify norm-orbit continuity with the topology on analytic
automorphisms in the manuscript, extend induction to arbitrary overlapping
atlases, pass to an extended analytic category, establish the analytic
extension universal property, or construct etale or quasi-etale sites.
The Harris specialization also remains a separate obligation.
