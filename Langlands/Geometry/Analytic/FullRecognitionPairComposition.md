# Composition of full-recognition pair systems

Author: Worker 36.

This module proves that the full-recognition pair systems of
`FullRecognitionPairSystems` compose. Let `g` and `g'` be strong maps of
local-domain enlargements, `A → B` and `B → C`. Take recognized affinoid subsets
`V`, `W`, `Z` of the three full recognitions with `g(V) ⊆ W` and `g'(W) ⊆ Z`.
Then the bounded map of the saturated composite on the pair `V`, `Z` is the
composite of the bounded maps of `g` on `V`, `W` and of `g'` on `W`, `Z`. This is
an equality of entire bounded algebra maps.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Definition 1.2.7, printed p.18 / PDF p.15: strong morphisms and their
  compatible affinoid morphisms on admissible chart pairs;
- the net axiom in §1.1, printed pp.13–14 / PDF pp.10–11. An intersection of
  two members of a net is covered locally by finitely many members contained
  in it;
- Proposition 1.2.15(i), printed pp.21–22 / PDF pp.18–19. It identifies
  morphisms with compatible systems of affinoid morphisms on all pairs of
  affinoid domains `V`, `V'` with `φ(V) ⊆ V'`.

A correspondence between morphisms and such systems must respect composition.
The source does not state this compatibility separately. The module proves it
for the systems constructed in `FullRecognitionPairSystems`, which is a derived
result. It does not prove the bijection of Proposition 1.2.15(i), the local
condition on admissible pairs, or Proposition 1.2.15(ii).

## Finite chart covers inside recognized subsets

Let `b` be an arbitrary `IndexedAffinoidAtlas.{u,v,w} K X`, `i` an original
chart, `W` a recognized subset of `b`, and `S` a subset of `X`.
`RecognizedChartCover b i W S` consists of finitely many original charts
`index m`, each with range contained in `range (b.chart i)` and in
`W.locus`, whose ranges cover `S`.

For compact `S` contained in both `range (b.chart i)` and `W.locus`,
`recognizedChartCover` constructs such a cover. It works in the published
recognition atlas `b.recognitionAtlas`. There `W` is a chart, and the chart
`b.originalRecognitionIndex i` has range `range (b.chart i)`. The published
`compactIntersectionChartCover` of that atlas uses its proved net axiom. It
gives finitely many recognized subsets contained in both charts and covering
`S`. Each of them is the union of the finitely many original charts of its own
witnessed recognition cover, by `cover_locus`. Those charts lie in it by
`component_subset`, hence in `range (b.chart i)` and in `W`. The finite sigma
type of all these components is reindexed by `Fintype.equivFin`. No
Hausdorffness of `X` and no closure of `b` under local domains is used.

## Source domain covers of a strong map

Let `h : StrongHom P Q` for arbitrary presentations in universes `u,v,w`, and
let `k` be a source chart. `isCompact_image_chart` records that
`h.baseMap '' range (P.atlas.chart k)` is compact. Let `T0` be a target chart
and `W` a recognized subset of `Q.atlas`, both containing this image.
`recognizedTargetChartCover` is the preceding cover of the image inside `T0`
and `W`.

`recognizedSourceDomainCover` is an actual `Domain.FiniteCover` of the whole
algebra of `k`. Its member `m` is the published `Domain.pullback`, along the
bounded pullback `h.pullback k T0`, of the restriction domain of the `m`-th
cover chart in `T0`. Its structural maps are the members' own base maps. The
covering property and `mem_recognizedSourceDomainCover_iff` follow from the
chart equation of `h`. A spectrum point lies in member `m` exactly when its
ambient image under `h` lies in the `m`-th target chart.

## The composite on one source local domain

Fix presentations `A`, `B`, `C` in universes `u,v,w`, strong maps
`g : StrongHom A.saturatedPresentation B.saturatedPresentation` and
`g' : StrongHom B.saturatedPresentation C.saturatedPresentation`. Write
`gg'` for their saturated composite, defined since both enlargements contain
all local domains. `toFullRecognitionTarget_pullback_comp_fullRecognitionPairs`
treats a source local domain `k` with `g(k) ⊆ W` and states

```text
(g.toFullRecognitionTarget.pullback k W).comp (g'.fullRecognitionPairs.pullback W Z)
  = gg'.toFullRecognitionTarget.pullback k Z.
```

The proof proceeds as follows.

1. Choose an original target chart `T0` with `g(k) ⊆ T0`. The image `g(k)`
   lies in `T0` and in `W`. Let `T m` be the charts of
   `g.recognizedTargetChartCover k T0 _ W _`. These are target local domains
   inside `T0 ∩ W` covering `g(k)`.
2. Use the cover `g.recognizedSourceDomainCover k T0 _ W _` of the whole
   algebra of `k`. Its member `m` consists of the points whose ambient image
   under `g` lies in `T m`.
3. By the published separation theorem `algebra_ext_of_restrict_eq`, it
   suffices to compare both sides after each structural map of this cover. Each
   member is a local domain of the source enlargement. By the published closure
   theorem, it is the range of a source chart `k_m` inside `k`. The published
   `inclusionOfSubset` factors the member's structural map through the original
   restriction from `k` to `k_m`. It therefore suffices to compare both sides
   after that restriction.
4. On `k_m`, with `g(k_m) ⊆ T m ⊆ W`, the strong restriction law of the
   composite into the target full recognition and the target-recognition
   formula through `T m` apply. The recovery formula for `g'` on the
   contained chart `T m` of `W` and the published `saturatedComp_pullback`
   through the intermediate chart `T m` also apply. Together with the published
   associativity `saturatedComp_assoc` and `pullback_congr`, they identify the
   left side with `gg'.toFullRecognitionTarget.pullback k_m Z`. The strong
   restriction law of `gg'` into full recognition identifies this with the
   right side after restriction.

The argument compares complete bounded algebra maps throughout. It never
infers algebra-map equality from equality of spectrum maps.

## Composition law

`fullRecognitionPairs_comp` states, for `g(V) ⊆ W` and `g'(W) ⊆ Z`,

```text
gg'.fullRecognitionPairs.pullback V Z
  = (g.fullRecognitionPairs.pullback V W).comp (g'.fullRecognitionPairs.pullback W Z).
```

The proof applies the extensionality theorem `RecognizedSubset.hom_ext` for
`V`. After restriction to any original chart `k` inside `V`, the recovery
formula of `FullRecognitionPairSystems` turns both sides into target-recognition
pullbacks on `k`. The preceding theorem identifies them.

## Scope

The composition law holds for arbitrary intermediate recognized subsets `W`. It
uses only the constructed local-domain enlargements, their proved closure, and
the published saturated composition and associativity. No directedness,
Hausdorffness of the ambient spaces, nontrivial valuation, reducedness or
nonemptiness is assumed.

The following remain further work: Berkovich's local condition for the family
of admissible pairs; the bijection between morphisms of the localized category
and pair systems in Proposition 1.2.15(i); the isomorphism criterion of
Proposition 1.2.15(ii); comparison with the quasi-isomorphism extension of
`FullRecognitionQuasiIso`; the analytic étale and quasi-étale sites; and the
Harris specializations.
