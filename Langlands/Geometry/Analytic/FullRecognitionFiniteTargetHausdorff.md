# Local Hausdorffness of preimages under finite target families

Module `Langlands.Geometry.Analytic.FullRecognitionFiniteTargetHausdorff`.

## Purpose

The target-local finiteness criterion
`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOverTargetLocalityStatement`
works on analytic spaces that need not be Hausdorff, and it may not assume a
global Hausdorffness hypothesis. The chart-recognition adapters
(`FiniteAlgebraChartRecognition.recognizedSubset`,
`FiniteChartParentRecognition`) need Hausdorffness of the literal finite
union being recognized, which in that criterion is the preimage
`V ∩ g⁻¹(W)` of a recognized target affinoid `W ⊆ U`. This module proves that
Hausdorffness from the finite neighborhood families supplied by the criterion's
hypothesis. It is a helper for the proof of that criterion; it introduces no
definitions and no statements.

## Provenance

The argument is the separation step implicit in Berkovich, *Étale cohomology
for non-Archimedean analytic spaces* (1993), Lemma 1.3.7, (a) implies (b)
(printed pp. 27–28; registered source `berkovich-1993-etale-cohomology`):
there the preimage of an affinoid domain is shown to be affinoid, hence in
particular Hausdorff. The source does not isolate this topological step; the
formulation and proof below are internal to this project.

## Declarations

### Pure topology (namespace `Langlands.Analytic.TargetLocalHausdorff`)

- `t2Space_of_ambient_separation`: a subset `s` of a topological space is a
  Hausdorff subspace if any two distinct points of `s` lie in ambient open sets
  `a`, `b` with `a ∩ b ∩ s = ∅`.
- `exists_ambient_separation`: conversely, a Hausdorff subspace `s` separates
  two distinct points of `s` by ambient open sets `a`, `b` with
  `a ∩ b ∩ s = ∅`. (Open sets of the subspace are traces of ambient open
  sets.)
- `t2Space_inter_preimage`: let `g : X → Y` be continuous, `V ⊆ X`, and
  `S ⊆ Y` a Hausdorff subspace. Suppose every `y ∈ S` admits a finite family
  `T` of subsets of `Y`, all containing `y`, with `⋃₀ T` a neighborhood of `y`
  and each `V ∩ g⁻¹(t)`, `t ∈ T`, a Hausdorff subspace. Then `V ∩ g⁻¹(S)` is a
  Hausdorff subspace.

### Specialization (namespace `Langlands.Analytic.AffinoidAtlasPresentation.StrongHom`)

For a strong map `g` between saturated presentations of
`A B : AffinoidAtlasPresentation.{u, v, w} K` (with independent universes and
any complete ultrametric normed field `K`, trivially valued allowed), and
subsets `V` of the source and `U` of the target:

- `t2Space_inter_preimage_of_recognizedFamilies`: assume that for each
  `x ∈ U` there is a finite set `I` of recognized target affinoids, all
  containing `x`, whose union of loci is a neighborhood of `x`, and such that
  for every `W ∈ I` some recognized source affinoid has locus exactly
  `V ∩ g⁻¹(W.locus)`. Then for every Hausdorff subspace `S ⊆ U`,
  `V ∩ g⁻¹(S)` is Hausdorff.
- `t2Space_inter_preimage_of_targetFamilies`: the same conclusion under
  literally the family hypothesis of `FiniteOverTargetLocalityStatement`
  (which additionally records `W.locus ⊆ U`, the chart-range inclusion and
  finiteness of the pullback; these extra parts are not used).
- `t2Space_inter_preimage_locus_of_targetFamilies`: the case `S = W.locus` for
  a recognized target affinoid `W` with `W.locus ⊆ U`; recognized loci are
  Hausdorff by the instance in `RecognizedAffinoidCategory`.

No openness of `V` or `U` and no global Hausdorffness is assumed.

## Proof

`t2Space_of_ambient_separation` pulls the ambient sets back along the
subtype inclusion. `exists_ambient_separation` applies `t2_separation` in the
subspace, writes both open sets as preimages of ambient open sets
(`isOpen_induced_iff`), and transfers disjointness.

For `t2Space_inter_preimage`, take distinct `x₁, x₂ ∈ V ∩ g⁻¹(S)`.

- If `g x₁ ≠ g x₂`, separate them in the Hausdorff subspace `S` by ambient open
  sets `a`, `b` with `a ∩ b ∩ S = ∅`; then `g⁻¹(a)`, `g⁻¹(b)` are open, contain
  `x₁`, `x₂`, and their intersection misses `V ∩ g⁻¹(S)`.
- If `g x₁ = g x₂ = y`, take the finite family `T` at `y`. Every `t ∈ T`
  contains `y`, so both points lie in the Hausdorff subspace `V ∩ g⁻¹(t)`;
  choose ambient open `a_t ∋ x₁`, `b_t ∋ x₂` with
  `a_t ∩ b_t ∩ V ∩ g⁻¹(t) = ∅`. Put `N = interior (⋃₀ T)`, which contains `y`
  because `⋃₀ T` is a neighborhood of `y`. The sets
  `(⋂_{t ∈ T} a_t) ∩ g⁻¹(N)` and `(⋂_{t ∈ T} b_t) ∩ g⁻¹(N)` are open (finite
  intersections, `Set.Finite.isOpen_biInter`, continuity of `g`) and contain
  `x₁`, `x₂`. A point `z` of their intersection lying in `V` has `g z ∈ t` for
  some `t ∈ T`, so `z ∈ a_t ∩ b_t ∩ V ∩ g⁻¹(t) = ∅`, a contradiction.

The specializations apply this with the continuous map `g.baseMap`, the family
`T = {W.locus | W ∈ I}` (finite as an image of a finite set, with
`⋃₀ T = ⋃_{W ∈ I} W.locus`), and the Hausdorff instance of the recognized
source affinoid `P` transported along `P.locus = V ∩ g⁻¹(W.locus)`.
