# Relative induction into arbitrary actual atlas-action targets

Author: Worker 56.

This module constructs the complete bounded equivariant extension into any
existing affinoid atlas presentation with a categorical group action. It
proves both inverse laws, uniqueness and naturality, giving a relative Hom
equivalence for the original-affinoid input functor. All equations compare
the continuous base maps, chosen chart indices and bounded pullbacks of the
original algebras.

The Lean namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.

## Parameters and precise correspondence

Let `K : Type u` be a complete normed ultrametric field, `G : Type v` a
topological group, `H` an open subgroup with witness `hH`, and
`X : NormContinuousSpace K H`. The latter is the geometric opposite of an
actual norm-continuous action on a finite positive-polyradius closed-ideal
quotient algebra. Let

```text
Y : Action (AffinoidAtlasPresentation.{u,max u v,v} K) G.
```

This is an actual categorical action on an existing atlas presentation.
It may have overlapping charts and need not be the realization of a
disjoint affinoid family. No additional continuity condition on the target
action is imposed. Each target action arrow already includes a continuous
base map and complete bounded chosen atlas data.

Write `L = localAtlasFunctor H`, `I = equivariantAtlasFunctor H hH` and
`R = Action.res (AffinoidAtlasPresentation.{u,max u v,v} K) H.subtype`.
The constructed equivalence is

```text
atlasExtensionEquiv H hH : (I.obj X ⟶ Y) ≃ (L.obj X ⟶ R.obj Y).
```

Its forward map restricts along the existing subgroup-equivariant normalized
unit. Its inverse constructs a bounded atlas arrow, rather than assuming an
extension object. This is relative to `L`: the original affinoid input and
the source of the restricted arrow are related by that specified functor.
The correspondence is in the category of monotone chosen atlas maps,
without identifying maps modulo refinement.

No finite-index, reducedness, radius-one or nonempty-spectrum hypothesis is
introduced. The algebras retain nilpotents and arbitrary positive radii.
The existing atlas construction omits empty-spectrum charts, and the
pullback assertions concern every actual chart.

## Actual copy maps and the normalized unit

`quotientCopyMap H hH X c` first takes the original bounded copy inclusion
`(copyMap H X c).atlasMap` into the disjoint coset atlas, then composes it
with `atlasComparisonHom H hH X` into the actual balanced quotient atlas.
The comparison uses the existing homeomorphism and bounded identity
pullbacks.

`quotientCopyMap_action` proves the complete-arrow correction equation

```text
quotientCopyMap(c) ≫ atlasActionMap(g)
  = (localActionMap(correction H g c)).atlasMap ≫ quotientCopyMap(g • c).
```

It combines the family copy-action equation, comparison equivariance,
atlas composition and associativity. `quotientAtlasHom_ext` proves that
two arrows out of the quotient atlas agree if their composites with every
copy agree. Its proof applies complete-arrow extensionality on the family
atlas, then cancels the comparison isomorphism. In particular, equality
of original algebra maps is not inferred from equality on spectrum points.

`unitAtlasMap_eq_quotientCopyMap` writes the normalized unit as the local
action by `identityRepresentative H` inverse followed by the identity-coset
copy. That chosen representative need not equal `1`.
`unitAtlasMap_action` proves that the unit followed by the induced action
at `c.out` equals the entire copy inclusion at `c`. Both results transport
the corresponding complete family-map equations through the comparison.

`atlasTargetAction_comp` records the target action law in geometric order:
`Y.ρ k ≫ Y.ρ g = Y.ρ (g * k)`. This lemma itself uses neither topology
on `G` nor a topological-group assumption.

## Constructed extension and complete inverse laws

Given `f : L.obj X ⟶ R.obj Y`, define `extendToAtlasMap H hH f` by

```text
atlasComparisonInv H hH X ≫
  assembleCopyAtlasMap H (fun c => f.hom ≫ Y.ρ c.out).
```

The existing copywise assembly constructs the continuous map, chosen
indices and bounded algebra pullbacks into the arbitrary atlas target.
Precomposition with the inverse comparison gives the actual map out of
the balanced quotient atlas.

`quotientCopyMap_extendToAtlasMap` proves that restricting this extension
to each complete copy recovers exactly `f.hom ≫ Y.ρ c.out`. It cancels
the two comparisons and uses the copy-assembly recovery equation.

`extendToAtlasMap_equivariant` compares the complete arrows

```text
atlasActionMap(g) ≫ extendToAtlasMap(f)
  = extendToAtlasMap(f) ≫ Y.ρ g.
```

The proof restricts to every copy, applies the correction equation and
the copy-recovery law, uses `f`'s subgroup equivariance, then combines
the target actions with `correction_spec`. Complete-copy extensionality
finishes the comparison. `extendToAtlas` bundles the constructed map and
this equation as a morphism `I.obj X ⟶ Y`.

`unitAtlasMap_extendToAtlasMap` proves

```text
unitAtlasMap H hH X ≫ extendToAtlasMap H hH f = f.hom.
```

It expands the normalized unit into the identity-coset copy, uses copy
recovery and subgroup equivariance of `f`, and cancels the target actions
at the identity representative and its inverse.

`restrictFromAtlas H hH p` is the composite of
`(equivariantAtlasUnit H hH).app X` with `R.map p`.
`restrictFromAtlas_extendToAtlas` follows from the complete unit triangle.
For the other inverse, `extendToAtlas_restrictFromAtlas` compares all
copies, moves the representative's action through `p` using equivariance,
and uses `unitAtlasMap_action`. These two proved laws define
`atlasExtensionEquiv`.

`extendToAtlas_unique` states that any full-group-equivariant `p` whose
composite with the complete unit equals `f.hom` is equal to
`extendToAtlas H hH f`. It applies injectivity of the constructed
equivalence and the restriction-extension law. The assertion retains all
chosen charts and original bounded pullbacks.

## Naturality and exact constructed formulas

`atlasExtensionEquiv_naturality_left` gives naturality under any original
bounded equivariant arrow `a : X' ⟶ X`:

```text
atlasExtensionEquiv (I.map a ≫ p)
  = L.map a ≫ atlasExtensionEquiv p.
```

It uses naturality of the complete normalized unit and associativity.
`atlasExtensionEquiv_naturality_right` gives naturality under every
bounded equivariant atlas-target arrow `q : Y ⟶ Z`, comparing restriction
of `p ≫ q` with restriction of `p` followed by `R.map q`. Its proof is
associativity. `extendToAtlas_naturality_left` and
`extendToAtlas_naturality_right` give the corresponding extension
equations; each follows by injectivity of the Hom equivalence, its
naturality and its two inverse laws.

For every actual source chart `c`,
`extendToAtlasMap_indexMap` identifies its chosen target chart with

```text
(Y.ρ c.val.out).indexMap (f.hom.indexMap ⟨PUnit.unit,c.property⟩).
```

`extendToAtlasMap_pullback` identifies its original bounded pullback with

```text
(f.hom.pullback ⟨PUnit.unit,c.property⟩).comp
  ((Y.ρ c.val.out).pullback (f.hom.indexMap ⟨PUnit.unit,c.property⟩)).
```

These are the actual chart index and contravariant composite supplied
by assembly; the comparison contributes an identity pullback. The index
proof is reflexive, and the pullback proof applies bounded algebra-map
extensionality and reflexivity.

`extendToAtlasMap_baseMap_copy` states that the point
`spectrumHomeomorph H X.unop hH ⟨c,x⟩` maps to
`(Y.ρ c.out).baseMap (f.hom.baseMap ⟨PUnit.unit,x⟩)`. The proof cancels
the actual spectrum homeomorphism with its inverse and unfolds assembly.
For every `g : G` and `x : LocalSpectrum H X.unop`,
`extendToAtlasMap_baseMap_mk` proves

```text
extendToAtlasMap(f).baseMap (TopologicalInduction.mk H g x)
  = (Y.ρ g).baseMap (f.hom.baseMap ⟨PUnit.unit,x⟩).
```

The original balanced quotient has the product-quotient topology. The
proof evaluates the already proved complete unit triangle and complete
equivariance at the unit point, then uses `g • [1,x] = [g,x]`. It therefore
applies to every representative, not only chosen ones. These evaluations
describe the base map of a previously constructed bounded atlas arrow.

## Original source, derived content and remaining scope

The motivating original is Vladimir G. Berkovich, *Etale equivariant sheaves
on p-adic analytic spaces*, unfinished 1995–1996 manuscript,
Construction 1.1.2, printed/PDF page 2. Registered source identifier:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
The publication-folder SHA256 is
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The manuscript constructs extension by applying the target action at a
representative on each coset copy. The present module derives that formula
and its relative complete-arrow Hom equivalence from the existing actual
copy assembly, bounded comparison, action and normalized unit. The
complete-arrow inverse laws, uniqueness, naturalities and exact bounded
chart formulas are derived implementation results. They are not
additional quoted claims about chosen presentations in the manuscript.

This relative Hom equivalence concerns original affinoid inputs and
categorical actions on existing atlas presentations in the stated
universes. It supplies neither the analytic automorphism-topology
comparison nor an extra continuity assertion for the target action.
Induction for arbitrary overlapping source atlases, identification modulo
refinement, a general analytic-space category, the analytic adjunction,
analytic etale and quasi-etale sites, and the Harris specialization remain
separate construction obligations.
