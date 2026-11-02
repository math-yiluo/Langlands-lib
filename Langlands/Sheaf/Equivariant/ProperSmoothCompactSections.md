# Proper compact sections of smooth equivariant sheaves

This module constructs proper spatial pullback between the compact-section
smooth representations of actual smooth equivariant sheaves. Its namespace is
`Langlands.Sheaf.Equivariant.ProperSmoothCompactSections`.

This is an internal construction from `ProperCompactSections`,
`LocalSupportComparison`, `SmoothSheafCompactSections` and `SmoothDirectImage`.
The first supplies support preservation for proper continuous equivariant maps;
the second identifies local-vanishing and stalk compact support by the identity
on sections; the third proves that all compact sections of a smooth sheaf form
a smooth representation; the fourth constructs smooth direct image as the smooth
part of ordinary direct image. No new assertion from Harris or Berkovich is
translated here.

## Scope and input data

The commutative coefficient ring `R`, group `G`, spaces and module carriers share
universe `u`. The group has a topology. Each space has a `G`-action with continuous
individual translations (`ContinuousConstSMul`). Let `f : C(X, Y)` be a continuous
equivariant map satisfying `IsProperMap f`. In particular, this is Mathlib's proper
map condition, which supplies compact inverse images in the existing support
argument; no additional Hausdorff or local compactness assumption is imposed.

The generic `pullback` construction takes smooth equivariant module sheaves `K`
on `Y` and `F` on `X`, and a genuine morphism of their underlying equivariant
sheaves

```text
b : K.obj ⟶ (DirectImage.sheaf f hf (ModuleCat R)).obj F.obj.
```

It requires neither stable-neighbourhood hypotheses nor `IsTopologicalGroup G`.
It uses only the existing smoothness of compact sections of `K` and `F`; it does
not require ordinary direct image to preserve smoothness.

## The compact-section morphism

`pullback f hf hp b` is a morphism from the smooth compact-section representation
of `K` to that of `F`. Its underlying representation morphism is the composite

```text
stalk-compact sections of K
  → local-vanishing compact sections of K
  → local-vanishing compact sections of F
  → stalk-compact sections of F.
```

The outer maps are the inverse and forward components of
`LocalCompactSections.stalkComparison`. The middle map is
`ProperCompactSections.pullback f hf hp b`. The two endpoint representations
are the underlying objects of `smoothSheafCompactSections`; the smooth
representation category is a full subcategory, so `ObjectProperty.homMk` bundles
the actual intertwiner without an extra equivariance or smoothness assumption.

`pullback_apply` states that the underlying section is
`(b.hom.app (op ActionOpens.top)).hom s.val`. Thus the map uses the original global
component of `b`. `pullback_comparison` expresses its compatibility with the
local/stalk support comparison. `pullback_inclusion_triangle` says that forgetting
compact support gives that same original global component followed by the
identity-on-global-sections direct-image comparison
`ProperCompactSections.globalIso`.

`pullback_id` gives the identity for the identity spatial map and identity
coefficient morphism. `pullback_precomp` and `pullback_postcomp` give naturality
in both smooth sheaves. For a second proper continuous equivariant map
`g : C(Y, Z)` and an actual map `a : L.obj → g_* K.obj`, `pullback_comp` identifies
the pullback for `a ≫ g_* b` along `g.comp f` with pullback along `g` followed by
pullback along `f`. Properness of the composite is `hq.comp hp`.

## Pullback from smooth direct image

The smooth-image constructions use `IsTopologicalGroup G` and
`HasStableNeighbourhoods G Y` to form the target smooth coreflector. The source
still has continuous individual translations. The identity law also uses stable
neighbourhoods on `X`; the composition law additionally uses them on `Z` for the
second target coreflector.

`natTrans f hf hp` is the natural transformation

```text
SmoothDirectImage.functor f hf ⋙ smoothSheafCompactSections R G Y
  ⟶ smoothSheafCompactSections R G X.
```

Its component at `F` is `pullback` applied to the actual inclusion of the smooth
direct image into the full ordinary direct image. `natTrans_apply` states that
its original section is `s.val.val`: the compact-support and local-smoothness
subtype proofs are forgotten. Naturality uses the original sheaf morphisms.

`lift_pullback` proves that applying compact sections to the universal smooth
lift `SmoothDirectImage.lift f hf b`, followed by `natTrans.app F`, recovers the
generic `pullback f hf hp b`. `natTrans_inclusion_triangle` records compatibility
with the original global-section maps. `natTrans_id` composes the compact-section
map of `SmoothDirectImage.idIso.hom` with the proper identity pullback and obtains
the identity on compact sections.

For two proper maps, `natTrans_comp` compares two actual morphisms. Applying
compact sections to `SmoothDirectImage.compMap`, then pulling back along the
spatial composite, equals pulling back first along `g` and then along `f`. This
uses the constructed lax composition map and does not require it to be invertible.

All displayed equations are proved by equality of the original section values:
the proof forgets full-subcategory morphism wrappers and support subtypes and
finishes by reflexivity. Support preservation and smoothness are supplied by
the imported proved constructions, rather than being new input hypotheses.

This module imposes no finite dimensionality, coefficient topology or
characteristic restriction. The coefficient map `b` remains genuine input data;
no inverse-image adjunction is asserted. It constructs ordinary-open equivariant
sheaf maps and compact-section representation maps. Higher cohomology, Godement
comparison, analytic or étale realization, arithmetic towers and the Harris
specialization remain obligations of the wider framework.
