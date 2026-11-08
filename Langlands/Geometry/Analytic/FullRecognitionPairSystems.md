# Compatible affinoid pair systems on full recognition atlases

Author: Worker 36.

This module starts the morphism description of Berkovich's Proposition
1.2.15(i). A morphism of analytic spaces gives a compatible system of affinoid
maps for *all* pairs of affinoid domains `V`, `V'` with `φ(V) ⊆ V'`. Such a
system is not a strong map between the maximal atlases. A large affinoid
domain of the source need not map into any single affinoid domain of the
target, so the system is indexed only by the admissible pairs.

The module defines these pair systems for actual atlas presentations. It
extends every strong map to all pairs consisting of a recognized source subset
and an admissible target chart, by bounded descent of the original pullbacks.
For strong maps between local-domain enlargements, this yields a pair system
on the two full recognition atlases. That system restricts to the original
bounded maps, and the identity extends to the identity.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Definition 1.2.7, printed p.18 / PDF p.15: a strong morphism has a
  continuous map, a target chart containing the image of each source chart,
  and compatible affinoid morphisms for all admissible chart pairs;
- the recognized affinoid domains and their canonical restrictions,
  Proposition 1.2.13(ii), printed p.21 / PDF p.18;
- Proposition 1.2.15(i), printed pp.21–22 / PDF pp.18–19. It identifies
  morphisms with pairs of a continuous map (with a local condition) and a
  system of compatible affinoid morphisms `φ_{V/V'}` for all pairs of
  affinoid domains with `φ(V) ⊆ V'`. Its proof begins: "It is easy to extend
  the system of compatible morphisms … for all pairs `V ∈ σ̂` and
  `V' ∈ τ̂'` with `φ(V) ⊆ V'`."

This module implements that extension step for strong maps. The full
recognition atlases are the constructed `σ̂`, `τ̂'`. The source does not spell
out the extension, so the descent construction here is derived. The module
does not prove the bijection of Proposition 1.2.15(i), its local condition,
the composition law for pair systems, or the isomorphism criterion of
Proposition 1.2.15(ii).

## Bounded descent into a recognized algebra

Let `a` be an arbitrary `IndexedAffinoidAtlas.{u,v,w} K X` and let `V` be a
recognized subset of `a`. Let `R` be any normed commutative `K`-algebra. Its
completeness is not required.

`IsChartCompatible V φ` says that `φ` assigns to every original chart `k` with
`range (a.chart k) ⊆ V.locus` a bounded map `R → a.algebra k`, such that

```text
(a.restriction k l hkl).comp (φ l) = φ k
```

whenever both charts lie in `V` and `k` lies in `l`. The family is indexed by
all contained charts, not by one chosen cover.

`gluingIndex_subset` shows that every chart of the chosen special cover
`V.val.gluingData` lies in `V`. `gluingFamily` restricts `φ` to these charts.
`gluingFamily_mapCompatible` proves the overlap equations of the finite section
algebra: both restrictions to the actual overlap chart equal `φ` on that chart.
`glue` applies the published bounded universal property `lift` of the section
algebra. It then transports the result along the inverse of the recognized
algebra's bounded equivalence `V.property.algebraEquiv`.

`originalRestriction_comp_glue` proves

```text
(V.originalRestriction k hk).comp (V.glue φ hφ) = φ k hk
```

for *every* contained chart `k`, not only for the charts of the special cover.
The canonical restriction `V.originalRestriction k` is built from the
published finite subordinate cover of `k`. On each subordinate chart, the
published formula `original_comp_originalRestriction` reduces the left side to
the section-algebra projection followed by an original restriction. That
projection of `lift` is the given family member. Chart compatibility then
identifies both sides on the subordinate chart. Algebra separation on the
actual finite domain cover gives equality of the entire bounded maps.

`hom_ext` shows that bounded maps into `V.algebra` are equal once they agree
after every canonical original restriction. Its proof uses the actual
component cover of the recognized algebra and the published identification of
its structural maps with canonical restrictions. `eq_glue` combines this with
the recovery formula: the glued map is the unique bounded map with the
prescribed restrictions. No algebra-map equality is inferred from spectra.

## Pair systems

For presentations `A : AffinoidAtlasPresentation.{u,v,w} K` and
`B : AffinoidAtlasPresentation.{u,v',w'} K`, with independent ambient and index
universes, `AdmissiblePairSystem A B` consists of

- a continuous map `baseMap : C(A.space, B.space)`;
- for every pair `i`, `j` with `baseMap '' range (A.atlas.chart i) ⊆
  range (B.atlas.chart j)`, a bounded map `pullback i j h` from the algebra of
  `j` to the algebra of `i`;
- the chart equation `chart_comm`: the target chart of the spectrum map of
  `pullback i j h` equals `baseMap` after the source chart;
- the restriction law `restriction_comm` for all source inclusions `i ⊆ i'`,
  target inclusions `j ⊆ j'` and admissible pairs `(i,j)`, `(i',j')`.

These are exactly the fields of `StrongHom` without `target_exists`.
`AdmissiblePairSystem.ext` proves equality from equal ambient maps and equal
bounded maps on every admissible pair.
`StrongHom.toAdmissiblePairSystem` forgets target existence.
`AdmissiblePairSystem.toStrongHom` restores it when every source chart has an
admissible target. The two round-trip lemmas hold by definition.

## Extension over recognized source subsets

Let `h : StrongHom P Q` for presentations in the same universes. For a
recognized subset `V` of `P.atlas` and an original target chart `j` with
`h.baseMap '' range V.chart ⊆ range (Q.atlas.chart j)`,
`recognized_admissible` shows that every contained original source chart `k`
is admissible for `j`. `recognizedChartPullbacks` is the family
`k ↦ h.pullback k j`. `recognizedChartPullbacks_compatible` is the strong
restriction law of `h` with the identity target restriction.

`recognizedSourceExtension h : AdmissiblePairSystem P.recognitionPresentation Q`
has ambient map `h.baseMap` and pullback `V.glue` of this family. Its fields
are proved as follows.

- Chart equation: every spectrum point of `V.algebra` is, by injectivity of
  `V.chart`, the image of a point of a special-cover chart `k` under the
  canonical restriction. The recovery formula turns the composite into
  `h.pullback k j`. Its chart equation and the canonical restriction's chart
  equation give the claim.
- Restriction law: for `U ⊆ V` and `j ⊆ j'`, `hom_ext` on `U` reduces the
  law to contained charts `k`. The published composition of canonical and
  recognized restrictions, the recovery formula, and the original strong
  restriction law identify both sides with `h.pullback k j'`.

`originalRestriction_comp_recognizedSourceExtension` restates the recovery
formula. `eq_recognizedSourceExtension` proves uniqueness. Any pair system on
`(P.recognitionPresentation, Q)` with ambient map `h.baseMap` and these
restrictions to all contained original charts equals the constructed one.

## Full recognition pairs

Let `A`, `B` be presentations in universes `u,v,w`, and let
`g : StrongHom A.saturatedPresentation B.saturatedPresentation` be a strong
map of their constructed local-domain enlargements. `toFullRecognitionTarget g`
is the saturated composite of `g` with the canonical identity-space strong map
`B.localDomainToFullRecognition`, whose pullbacks are canonical restrictions.
Both enlargements contain all local domains by the published closure theorem,
so the composite is defined.

`toFullRecognitionTarget_pullback` uses the published composition formula
`saturatedComp_pullback`. For every source local domain `S`, target local
domain `T` with `g(S) ⊆ T`, and recognized target subset `W ⊇ T`:

```text
pullback S W = (g.pullback S T).comp (W.originalRestriction T).
```

`fullRecognitionPairs g` is the source extension of this composite, an
`AdmissiblePairSystem A.fullRecognitionPresentation B.fullRecognitionPresentation`.
The source full recognition presentation is definitionally the recognition
presentation of the source enlargement. Its ambient map is `g.baseMap`
(`fullRecognitionPairs_baseMap`). For recognized `V`, `W` with `g(V) ⊆ W`,
`originalRestriction_comp_fullRecognitionPairs` proves

```text
(V.originalRestriction S).comp (pullback V W)
  = (g.pullback S T).comp (W.originalRestriction T)
```

for all source local domains `S ⊆ V` and target local domains `T ⊆ W` with
`g(S) ⊆ T`. Thus the system extends `g` through the canonical restrictions on
both sides.

`fullRecognitionPairs_id` proves that the identity of `A.saturatedPresentation`
extends to the pair system of `StrongHom.id A.fullRecognitionPresentation`. The
proof applies uniqueness. On each contained local domain, both sides are the
canonical restriction from `W`, by the published composition of canonical and
recognized restrictions and the identity restriction law.

For a strong map `f : StrongHom A B` of the original presentations with
intrinsic coherence `hf`, `fullRecognitionPairsOfCoherent f hf` applies the
construction to the published local-domain extension `f.saturationExtension hf`.
Its ambient map is `f.baseMap`.

## Scope

The descent works for arbitrary atlases and arbitrary normed test algebras. It
assumes no closure, directedness, Hausdorffness of the ambient space,
nontrivial valuation, reducedness or nonemptiness. The full recognition
specialization uses only the constructed local-domain enlargements and their
proved closure.

The following remain further work: the composition law of pair systems, which
needs a covering of source recognized subsets by local domains mapping into
target local domains inside `W`; Berkovich's local condition for the family of
admissible pairs; and the bijection between morphisms of the localized category
and pair systems in Proposition 1.2.15(i). Also open are the isomorphism
criterion of Proposition 1.2.15(ii), comparison with the quasi-isomorphism
extension of `FullRecognitionQuasiIso`, arbitrary equivalent-net comparisons,
the analytic étale and quasi-étale sites, and the Harris specializations.
