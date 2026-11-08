# The isomorphism criterion through full-recognition pair systems

Author: Worker 36.

This module proves the sufficient direction of Berkovich's isomorphism
criterion, Proposition 1.2.15(ii), for strong maps of local-domain
enlargements. The criterion is stated through their full-recognition pair
systems. A map satisfying it is a strong quasi-isomorphism, hence an
isomorphism in the localized category. The module also shows that the
localized morphism between full recognitions built from the pair system of any
strong quasi-isomorphism is an isomorphism.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Definition 1.2.9, printed p.19 / PDF p.16: a quasi-isomorphism is a strong
  morphism with an ambient homeomorphism that identifies each admissible
  source chart with an affinoid domain of the target chart;
- the passage after Proposition 1.2.10, printed p.20 / PDF p.17: analytic
  spaces form the category of fractions with respect to quasi-isomorphisms;
- Proposition 1.2.15(ii), printed p.22 / PDF p.19: a morphism `φ` is an
  isomorphism if and only if `φ` induces a homeomorphism, `φ(τ̂) = τ̂'`, and
  `(V, 𝒜_V) → (V', 𝒜'_{V'})` is an isomorphism for every `V ∈ τ̂`, where
  `V' = φ(V)`. The source proves (ii) from (i).

`IsomorphismCriterion` transcribes the conditions of the "if" direction for
the constructed maximal atlases (full recognitions) and pair systems. It asks
that each recognized image be recognized, which is the inclusion `φ(τ̂) ⊆ τ̂'`
the argument uses. The equality `φ(τ̂) = τ̂'` is not required. The proof is
derived; it does not follow the source's route through part (i). The "only if"
direction is not proved here.

## Representations of the whole spectrum

For presented affinoid algebras `A`, `B` and a bounded map `f : A → B`
representing the whole spectrum of `A`, the full universal property gives a
bounded map `univInverse` with `univInverse ∘ f = id`
(`Represents.univInverse_comp`). Uniqueness of the factorization of `f` itself
gives `f ∘ univInverse = id` (`Represents.comp_univInverse`).
`Represents.univEquiv` is the resulting `BoundedAlgEquiv` (published
`BoundedAlgEquiv.ofHomInv`), whose forward map is `f`.

For an arbitrary atlas and an original chart `i`, the recognized subset
`originalRecognitionIndex i` contains the chart range
(`originalRecognitionIndex_range_subset`). Its canonical restriction to `i`
represents the whole spectrum
(`originalRecognition_originalRestriction_represents_univ`): the published
representation theorem gives the preimage of the chart range, and this is the
whole spectrum because both ranges agree. Hence
`originalRecognitionRestrictionEquiv i` is a bounded algebra equivalence whose
forward map is that restriction.

## Quasi-isomorphisms from recognized images

Let `g : StrongHom A.saturatedPresentation B.saturatedPresentation`, and write
`P` for its full-recognition pair system.

`isQuasiIso_of_originalImages` assumes that `g.baseMap` is a homeomorphism.
It also assumes that for every source local domain `S` there are a recognized
target subset `W` and an admissibility proof for `(orig S, W)` with
`W.locus = g(S)`, and a bounded algebra equivalence `e` whose forward map is
`P(orig S, W)`. It concludes `g.IsQuasiIso`. For an admissible pair `(S, T)`
the proof argues as follows.

1. `W ⊆ orig T`, since `g(S) ⊆ T`. The characterization of
   `FullRecognitionPairSystems`, applied to `S ⊆ orig S` and `T ⊆ orig T`, and
   the pair-system restriction law for `W ⊆ orig T` give
   `g(S,T) ∘ ι = σ ∘ e ∘ r`. Here `ι` and `σ` are the original recognition
   restriction equivalences for `T` and `S`, and `r` is the recognized
   restriction from `orig T` to `W`.
2. Hence `g(S,T) = σ ∘ e ∘ r ∘ ι⁻¹`, an equality of entire bounded maps.
3. `r` represents the preimage of `W` (published `restriction_represents`).
   Postcomposition with the equivalences `e` and `σ` (published
   `Represents.postcomp_equiv`) and precomposition with `ι⁻¹` (published
   `Represents.precomp_equiv`) keep the representation. The precomposition
   transports the locus along the spectrum homeomorphism of `ι`.
4. By the chart equation of the canonical restriction, that transported locus
   is exactly `chartImageLocus S T`, the preimage of `g(S)` in `T`.

`IsomorphismCriterion g` is the conjunction of the homeomorphism condition
and, for every recognized source subset `V`, the existence of a recognized `W`
with `W.locus = g(V)`, an admissibility proof, and a bounded algebra
equivalence whose forward map is `P(V, W)`.
`IsomorphismCriterion.isQuasiIso` applies the preceding theorem to
`V = orig S`. Its locus is the range of `S`.

## Localized consequences

`saturatedHom g` is `g` as a morphism of the saturated strong category between
the published objects `ofSaturation A` and `ofSaturation B`.
`IsomorphismCriterion.isIso_localizationFunctor_map` proves that its image in
the localized category is an isomorphism, by the published `localizedQuasiIso`.

`isIso_fullRecognitionLocalizedHom` shows that for every strong
quasi-isomorphism `g`, the morphism `fullRecognitionLocalizedHom g` of
`PairSystemLocalizedMorphisms` is an isomorphism. The canonical maps
`localDomainToFullRecognitionHom A` and `B` are quasi-isomorphisms
(`localDomainToFullRecognition_isQuasiIso` of `LocalDomainSubnetRecognition`),
so their localized images are isomorphisms. The composite of `saturatedHom g`
with the target canonical map is `toFullRecognitionTargetHom g`, whose image is
therefore an isomorphism. The comparison theorem of
`PairSystemLocalizedMorphisms` rewrites this image as the localized source
canonical map followed by `fullRecognitionLocalizedHom g`. Cancelling that
isomorphism (Mathlib's `IsIso.of_isIso_comp_left`) gives the claim.
`IsomorphismCriterion.isIso_fullRecognitionLocalizedHom` is the case where `g`
satisfies the criterion.

## Scope

The criterion and its proof use the constructed recognized subsets,
pair-system maps and canonical restrictions. They assume no closure beyond the
constructed local-domain enlargements, and no directedness, Hausdorffness,
nontrivial valuation, reducedness or nonemptiness. The following remain
further work: the "only if" direction of Proposition 1.2.15(ii) (recognized
images and isomorphic pair maps for quasi-isomorphisms, and equality of the
recognized families); the full bijection of Proposition 1.2.15(i); the
analytic étale and quasi-étale sites; and the Harris specializations.
