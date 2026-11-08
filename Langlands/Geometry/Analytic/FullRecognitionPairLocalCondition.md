# Berkovich's local condition for full-recognition pair systems

Author: Worker 36.

This module defines the local condition on pair systems from Berkovich's
Proposition 1.2.15(i). It proves that the full-recognition pair systems of
`FullRecognitionPairSystems` satisfy it.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- the quasinet and net definitions in §1.1, printed pp.13–14 / PDF pp.10–11;
- Proposition 1.2.15(i), printed pp.21–22 / PDF pp.18–19. Its pairs consist of
  a continuous map `φ : X → X'` "such that for each point `x ∈ X` there exist
  neighborhoods `V_1 ∪ … ∪ V_n` of `x` and `V'_1 ∪ … ∪ V'_n` of `φ(x)` with
  `x ∈ V_1 ∩ … ∩ V_n` and `φ(V_i) ⊂ V'_i`, where `V_i ⊂ X` and `V'_i ⊂ X'` are
  Φ-affinoid domains", together with a system of compatible morphisms on all
  admissible pairs of affinoid domains.

`AdmissiblePairSystem.LocalCondition` transcribes this local condition for the
chart families of arbitrary atlas presentations. Its proof for the constructed
full-recognition pair systems is derived; the source states the condition but
does not prove it for the extension. The bijection of Proposition 1.2.15(i) and
Proposition 1.2.15(ii) remain further work.

## The local condition

For `A : AffinoidAtlasPresentation.{u,v,w} K`,
`B : AffinoidAtlasPresentation.{u,v',w'} K` and
`p : AdmissiblePairSystem A B`, `p.LocalCondition` says the following. For every
point `x` of `A.space` there is a finite set `I` of pairs of a source chart index
and a target chart index such that

- `x` lies in the range of every source chart of `I`;
- `p.baseMap` maps the range of each source chart of `I` into the range of its
  paired target chart, so every pair of `I` is admissible;
- the union of the source ranges is a neighborhood of `x`;
- the union of the target ranges is a neighborhood of `p.baseMap x`.

A finite set of index pairs is the same as the source's finite list of
pairs `(V_i, V'_i)`. A repeated pair contributes nothing new to the unions.
Since the source union is a neighborhood of `x`, it contains `x`, so `I` is
nonempty.

## Chart-level proof for saturated sources

Let `h : StrongHom P Q` for presentations in universes `u,v,w`, where every
local domain of `P.atlas` is an original chart (`P.atlas.HasAllLocalDomains`).

`exists_chart_inter_preimage` takes a source chart `k`, a target chart `j`
containing the image of `k`, and a target chart `l` inside `j`. It gives a
source chart whose range is exactly
`range (P.atlas.chart k) ∩ h.baseMap ⁻¹' range (Q.atlas.chart l)`. This range
is the local domain of `k` obtained by the published `Domain.pullback`, along
the bounded pullback `h.pullback k j`, of the restriction domain of `l` in `j`.
The chart equation of `h` identifies its locus. The closure hypothesis then
supplies a chart with that range.

`localCondition_of_hasAllLocalDomains` proves the local condition for
`h.toAdmissiblePairSystem` at a point `x` with image `y`.

1. The quasinet axiom of the source atlas gives finitely many source charts
   `U` containing `x` with union a neighborhood of `x`. The quasinet axiom of
   the target atlas gives finitely many target charts `V` containing `y` with
   union `N` a neighborhood of `y`. For each `U`, a target chart `T U`
   contains the image of `U`.
2. For each `U` and `V`, the net axiom of the target atlas applies to
   `range (T U) ∩ V`. Through the published `isQuasinet_restrictedFamily_iff`,
   it gives finitely many target charts `W` inside `range (T U) ∩ V`, each
   containing `y`, with union a neighborhood of `y` relative to
   `range (T U) ∩ V`.
3. The finite set `I` consists of the pairs `(piece U V W, V)`. Here
   `piece U V W` is the chart given by `exists_chart_inter_preimage`, with
   range `U ∩ h⁻¹(W)`. Each piece
   contains `x` and maps into `W ⊆ V`.
4. Choose ambient neighborhoods `O U V` of `y` witnessing the relative
   neighborhoods of step 2. The set
   `(⋃ U) ∩ h⁻¹(N ∩ ⋂ O U V)` is a neighborhood of `x`, and every one of its
   points lies in some piece. Indeed, such a point `z` lies in some `U`, its
   image lies in some `V`, in `T U` and in `O U V`, hence in some `W`.
5. Every `V` occurs in `I`, because some source chart `U` exists and the
   relative neighborhood of step 2 contains `y`. Therefore the union of the
   target ranges is `N`.

The proof uses only the quasinet and net axioms of the two original atlases,
continuity of the ambient map, and the source closure hypothesis. It needs no
Hausdorffness of the ambient spaces and no further choice of targets.

## Full recognition

`fullRecognitionPairs_localCondition` proves that for every strong map
`g : StrongHom A.saturatedPresentation B.saturatedPresentation`, the pair system
`g.fullRecognitionPairs` satisfies the local condition. The source enlargement
contains all local domains by the published closure theorem, so the chart-level
theorem applies to `g`. Its finite set is mapped by `originalRecognitionIndex`
on both sides. By the published `recognitionAtlas_original_range`, these
recognized subsets have exactly the same ranges as the original local domains.
The ambient map of `g.fullRecognitionPairs` is `g.baseMap`. Hence all four
requirements transfer unchanged.

## Scope

The local condition and its proof involve no algebra maps; the compatible
bounded maps are those of `FullRecognitionPairSystems`. The following remain
further work: the converse direction of Proposition 1.2.15(i), from a pair
system with the local condition to a morphism of the localized category, and the
bijection itself. Also open are Proposition 1.2.15(ii), arbitrary equivalent-net
comparisons, the analytic étale and quasi-étale sites, and the Harris
specializations.
