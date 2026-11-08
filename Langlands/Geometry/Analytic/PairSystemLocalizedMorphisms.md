# Morphisms of the localized category from pair systems with the local condition

Author: Worker 36.

This module implements the converse direction of Berkovich's Proposition
1.2.15(i). A compatible pair system with the local condition determines a
morphism in the localized category of analytic spaces. For the full-recognition
pair system of a strong map `g`, the constructed morphism recovers `g` through
the canonical maps into full recognition.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- the quasinet and net definitions in §1.1, printed pp.13–14 / PDF pp.10–11;
- the passage after Proposition 1.2.10, printed p.20 / PDF p.17: analytic
  spaces form the category of fractions of strong morphisms with respect to
  quasi-isomorphisms;
- Proposition 1.2.15(i) and its proof, printed pp.21–22 / PDF pp.18–19. For
  the converse direction the proof says: "Conversely, suppose that we have a
  pair of the above form. To verify that it comes from a morphism of
  Φ-analytic spaces, it suffices to show that the collection `σ` of all
  `V ∈ τ̂` such that `φ(V) ⊂ V'` for some `V' ∈ τ̂'` is a net." It then derives
  the net property from the local condition.

The admissible source net, its net property and the restricted strong map
transcribe this argument for actual atlas presentations. The source leaves the
resulting morphism implicit. Its construction here, through the localized
category and the quasi-isomorphic inclusion of the net, is derived. So is the
comparison with `g`. The bijection itself is not proved here: neither that
the constructed morphism determines the pair system, nor that every localized
morphism arises this way.

## Admissible sources and their net

Let `A`, `B` be presentations in universes `u,v,w` and
`p : AdmissiblePairSystem A B`. `p.AdmissibleSource i` says that some target
chart `j` contains `p.baseMap '' range (A.atlas.chart i)`.
`admissibleSource_of_subset` shows that admissibility passes to every smaller
source chart.

`isNetSelection_admissibleSource` proves that, under `p.LocalCondition`, the
admissible source charts form a net (`IsNetSelection`).

- Quasinet: at a point `x`, the local condition gives finitely many admissible
  pairs whose source charts contain `x`, with source union a neighborhood of
  `x`. Their source ranges are the required finite family.
- Net: let `U`, `V` be admissible source charts. The original chart family is
  a net, so its members contained in `U ∩ V` form a quasinet of `U ∩ V` with
  the induced topology. Each such member lies in the admissible `U`, so it is
  admissible. The restricted admissible family therefore contains the
  restricted original family, and `IsQuasinet.mono` gives the quasinet
  property.

`admissibleNetStrongHom` is the strong map from
`A.netSubpresentation p.AdmissibleSource _` (the selected net
subpresentation of `SubnetRecognitionEquivalence`, with the original algebras
and restrictions) to `B`. Its
ambient map is `p.baseMap`, target existence is the admissibility of each
selected chart, and its bounded maps, chart equation and restriction law are
those of `p`. `admissibleNetStrongHom_baseMap` and
`admissibleNetStrongHom_pullback` record this.

`hasAllLocalDomains_admissibleNet` proves that the admissible net subatlas
contains all its local domains when `A.atlas` does. A local domain of an
admissible chart is also a local domain of the original atlas. Hence it is the
range of an original chart inside the admissible chart, which is admissible
by downward closure.

## The localized morphism

Now let `A`, `B` be saturated presentations, `p` a pair system on them, and
`hp : p.LocalCondition`.

- `admissibleNet p hp` is the saturated object given by the admissible net
  subpresentation and the preceding closure theorem.
- `admissibleNetInclusion p hp` is the identity-space inclusion
  `strongNetSubatlasInclusion` of `SubnetRecognitionEquivalence`.
  `admissibleNetInclusion_isQuasiIso` records the proof there that it is a
  quasi-isomorphism.
- `admissibleNetMap p hp` is `admissibleNetStrongHom`, as a morphism of the
  saturated strong category.

`pairSystemLocalizedHom p hp` is the composite, in the published localized
category, of the inverse of the localized inclusion (`localizedQuasiIso`) with
the localized restricted map. It is a morphism from `A` to `B`.

`localizationFunctor_map_admissibleNetInclusion_comp` shows that precomposing
with the localized inclusion gives the localized restricted map.
`localizedSpaceFunctor_map_pairSystemLocalizedHom` shows that the underlying
continuous map is `p.baseMap`. Apply the published localized space functor to
the preceding identity and use that the inclusion has the identity ambient map.

## Corestriction to a target net

For a strong map `f : StrongHom A B` and a net selection `P` of target charts
containing an admissible target for every source chart,
`corestrictNetSubatlasTarget` is the strong map into
`B.netSubpresentation P _` with the same ambient map and bounded maps. Suppose
the source and the selected net contain all local domains.
`corestrictNetSubatlasTarget_saturatedComp` then proves that its saturated
composite with the identity-space inclusion is `f`. The published
`ext_of_saturated` reduces this to one admissible selected target per source
chart. There `saturatedComp_pullback` and the identity restriction law give the
original bounded map.

## Full recognition: the construction recovers `g`

Let `g : StrongHom A.saturatedPresentation B.saturatedPresentation`. Its
full-recognition pair system satisfies the local condition (unit
`FullRecognitionPairLocalCondition`). The objects `ofFullRecognition A` and
`ofFullRecognition B` of `FullRecognitionStrongInverse` are saturated.
`fullRecognitionLocalizedHom g` is `pairSystemLocalizedHom` for this pair
system, a morphism from `ofFullRecognition A` to `ofFullRecognition B`.

`fullRecognitionPairs_admissibleSource_original` shows that every original
local domain, viewed as a recognized subset, is an admissible source. Its
image under `g` lies in a target local domain, whose recognized subset has the
same range. Hence
`localDomainToFullRecognition_admissibleTargets` holds for the canonical
identity-space map `A.localDomainToFullRecognition`, and
`localDomainToAdmissibleNet` is its corestriction to the admissible net.

`localDomainToAdmissibleNet_saturatedComp_admissibleNetStrongHom` proves that
the corestricted canonical map followed by the restricted pair system is
`g.toFullRecognitionTarget`. The base maps agree definitionally
(`localDomainToAdmissibleNet_saturatedComp_baseMap`), so `ext_of_saturated`
applies. For a source local domain `S`, take the intermediate recognized subset
of `S` and the target recognized subset of a target local domain containing
`g(S)`. `saturatedComp_pullback` gives the canonical restriction from that
recognized subset to `S`, followed by the pair-system map. The recovery
formula of `FullRecognitionPairSystems` identifies this with the
target-recognition pullback of `g`.

The morphisms `localDomainToFullRecognitionHom A`, `toFullRecognitionTargetHom g`
and `localDomainToAdmissibleNetHom g` are these strong maps as morphisms of the
saturated strong category.
`localizationFunctor_map_comp_fullRecognitionLocalizedHom` proves

```text
Q(localDomainToFullRecognitionHom A) ≫ fullRecognitionLocalizedHom g
  = Q(toFullRecognitionTargetHom g),
```

where `Q` is the localization functor. The corestriction theorem factors the
canonical map through the inclusion, the preceding theorem factors
`toFullRecognitionTargetHom g` through the restricted map, and the inverse of
the localized inclusion cancels. The canonical map is a quasi-isomorphism
(`localDomainToFullRecognition_isQuasiIso` of `LocalDomainSubnetRecognition`),
so this determines `fullRecognitionLocalizedHom g` as the
localized `g` transported to the full recognitions.

## Scope

The construction uses the actual net subpresentation, its quasi-isomorphic
inclusion and the published localization. It assumes no closure beyond the
saturation of the two objects, no directedness, Hausdorffness, nontrivial
valuation, reducedness or nonemptiness. The following remain further work:
uniqueness of the pair system determined by a localized morphism; the
statement that every localized morphism arises from a pair system with the
local condition; independence from equivalent presentations; Proposition
1.2.15(ii); the analytic étale and quasi-étale sites; and the Harris
specializations.
