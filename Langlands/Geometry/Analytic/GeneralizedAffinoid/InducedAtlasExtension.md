# Bounded quotient-atlas realization of affinoid-family extension

Author: Worker 56.

This module realizes the constructed bounded family extension on the original
balanced quotient atlas. The extension is equivariant for the full group, and
its composite with the normalized unit is the original bounded atlas map.
Naturality, chart indices, bounded pullbacks and the formula at every quotient
representative identify the constructed map, including its algebra data.

The Lean namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.

## Inputs and precise output

Let `K : Type u` be a normed ultrametric field, `G : Type v` a group with a
topology, `H` a subgroup, and `X : NormContinuousSpace K H`. The latter is
the geometric opposite of an actual norm-continuous action on a finite
positive-polyradius closed-ideal quotient algebra. The original algebra is
`X.unop.obj.V`. Let `Y : Action (AffinoidFamily.{u,v} K) G` be an actual
categorical group action on genuine affinoid families, and let

```text
f : (localFunctor H).obj X ⟶ (Action.res _ H.subtype).obj Y.
```

Thus `f` is an actual subgroup-equivariant bounded family map, with a chosen
target component and an original bounded algebra pullback. No additional
joint-continuity or analytic automorphism-topology condition on `Y` is imposed.

The first two lemmas, `extendFamily_naturality_left` and
`extendFamily_naturality_right`, use these hypotheses alone. They give the
inverse-direction naturality of the existing `familyExtensionEquiv`.
Each proof applies injectivity of that equivalence, rewrites its existing
naturality equation, and uses the restriction-extension inverse law.

All subsequent declarations additionally assume that `G` is a topological
group, `K` is complete, and `hH : IsOpen (H : Set G)`. These assumptions
provide the actual balanced quotient atlas and family-atlas realization.
The result `extendAtlas H hH f` is an arrow from
`(equivariantAtlasFunctor H hH).obj X` to the existing atlas realization of
`Y`, in the category of full-group actions on
`AffinoidAtlasPresentation.{u,max u v,v} K`.

No finite-index, reducedness, radius-one or nonempty-spectrum assumption is
introduced. The family constructions retain empty components and their
algebras. Atlas realization uses the existing nonempty-spectrum chart subtype
on both sides, so components without spectrum points contribute no charts.
The assertions about bounded pullbacks concern every actual chart.

## Actual bounded quotient-atlas extension

`atlasComparisonInv_equivariant` and `atlasComparisonInv_naturality` expose
the inverse equations of the existing equivariant natural comparison
isomorphism. They follow from the inverse action morphism's equivariance and
the inverse natural transformation's naturality, respectively. Their
equalities retain base maps, chart choices and bounded pullbacks.

`extendAtlasMap H hH f` is the composite

```text
atlasComparisonInv H hH X ≫ (extendFamilyMap H f).atlasMap.
```

The first map uses the actual quotient-to-disjoint-family homeomorphism and
bounded identity pullbacks on the unchanged original chart algebras. The
second realizes the constructed copywise bounded extension. Thus this
composite supplies actual chart indices and bounded algebra maps; an
extension is not an assumed input.

`extendAtlasMap_equivariant` proves

```text
atlasActionMap(g) ≫ extendAtlasMap(f)
  = extendAtlasMap(f) ≫ (Y.ρ(g)).atlasMap.
```

Its proof uses the inverse comparison's complete equivariance, the existing
whole-family extension equivariance, the actual atlas-map composition law,
and associativity. `extendAtlas` bundles that constructed map and equation
as the indicated full-group equivariant atlas morphism.

`unitAtlasMap_extendAtlasMap` proves the complete normalized-unit triangle

```text
unitAtlasMap H hH X ≫ extendAtlasMap H hH f = f.hom.atlasMap.
```

The proof cancels the forward and inverse atlas comparisons and realizes the
existing complete bounded-family unit triangle. It does not normalize the
chosen identity-coset representative to `1`, nor deduce equality of bounded
algebra maps from their values on spectrum points.

`extendAtlasMap_naturality_left` states that precomposing `f` with any
original bounded equivariant arrow `a : X' ⟶ X` extends to precomposition
by `atlasMap H hH a`. It combines the inverse-direction family naturality
with the inverse comparison naturality. `extendAtlasMap_naturality_right`
states that postcomposing `f` with the restriction of any bounded
equivariant family arrow `q : Y ⟶ Z` extends to postcomposition by
`q.hom.atlasMap`. It uses the family naturality and atlas composition law.
Both compare complete chosen atlas maps.

## Exact constructed data and representative formula

For an actual source chart `c`, `extendAtlasMap_indexMap` identifies the
underlying target family component with

```text
(Y.ρ c.val.out).indexMap (f.hom.indexMap PUnit.unit).
```

The nonempty target-chart witness is supplied by the existing family-atlas
construction. `extendAtlasMap_pullback` identifies the actual bounded
pullback with

```text
(f.hom.pullback PUnit.unit).comp
  ((Y.ρ c.val.out).pullback (f.hom.indexMap PUnit.unit)).
```

The index equation is reflexive; the pullback equation follows by bounded
algebra-map extensionality and reflexivity. The comparison contributes only
an algebra identity.

`extendAtlasMap_baseMap_copy` states that on the copy indexed by `c : G/H`,
the base map sends `spectrumHomeomorph H X.unop hH ⟨c,x⟩` to
`(Y.ρ c.out).spectrumMap (f.hom.spectrumMap ⟨PUnit.unit,x⟩)`. Its proof
cancels the actual homeomorphism and its inverse and unfolds the copywise
extension.

`extendAtlasMap_baseMap_mk` gives the formula for every representative
`g : G` and every `x : LocalSpectrum H X.unop`:

```text
extendAtlasMap(f).baseMap ([g,x])
  = (Y.ρ g).spectrumMap (f.hom.spectrumMap ⟨PUnit.unit,x⟩).
```

Here `[g,x]` means `TopologicalInduction.mk H g x` in the original balanced
quotient with its product-quotient topology. The proof evaluates the complete
unit triangle at `x`, uses the existing exact unit formula `[1,x]`, then
evaluates complete extension equivariance at that unit point and uses
`g • [1,x] = [g,x]`. Consequently the formula holds independently of all
chosen quotient representatives. These point formulas identify the base map
of an already constructed bounded atlas arrow.

## Original source and internally derived content

The motivating original is Vladimir G. Berkovich, *Etale equivariant sheaves
on p-adic analytic spaces*, unfinished 1995–1996 manuscript,
Construction 1.1.2, printed/PDF page 2. Registered source identifier:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
The publication-folder SHA256 is
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The exact member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The original extends a morphism on each coset copy by applying the target
action at the chosen representative. This module derives the bounded
quotient-atlas realization from the actual family extension and comparison
constructed in the imported modules. The inverse naturality, complete
bounded equivariance and unit triangle, exact chart data and
arbitrary-representative point formula are internally derived implementation
results. They are not additional quoted claims from the manuscript.

This module supplies existence and the displayed equations for targets
realized from categorical affinoid-family actions. It does not establish a
Hom equivalence for arbitrary chosen atlas morphisms, extension to arbitrary
analytic targets, induction on overlapping analytic atlases, the analytic
automorphism-topology comparison, an analytic adjunction, analytic sites or
the Harris specialization. Those remain separate construction obligations.
