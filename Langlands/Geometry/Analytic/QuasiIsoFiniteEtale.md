# Finite étaleness of full quasi-isomorphisms

Author: Worker 208.

This derived internal prerequisite uses the Library's full-domain universal
properties and recognized-image constructions. It supplies bounded algebra
comparisons and finite étaleness for the actual saturation extension of a
coherent strong quasi-isomorphism. It does not prove localized étale
composition, right cancellation, or unrestricted pointwise lifting.

Work over a complete ultrametric normed field `K : Type u`, with independent
space and atlas-index universes `v` and `w`. Let `f : StrongHom A B`, assume
`hf : f.IsQuasiIso` and `hc : f.HasCoherentPullbacks`, and set
`g = f.saturationExtension hc`. No separation or compactness hypothesis is
used. The objects called recognized subsets below belong to the saturated
atlases of `A` and `B`.

## Actual bounded-map comparisons

`saturationExtension_pullback_saturatedImage` identifies `g`'s pullback on a
saturated source chart and its entire image with the inverse bounded
`saturatedImageEquiv`. Its proof compares the image local domain with the
chosen saturated representative, then applies uniqueness of local-domain
pullback using the structural equation over a containing original chart.
This establishes equality of bounded maps using the universal property.

`saturationExtension_fullRecognitionPairs_pullback_recognizedImage` extends
this equality to every recognized source subset `V` and its recognized
image. The proof tests bounded maps on the original charts of `V`, uses the
pair-system restriction equation, and cancels the bounded image equivalence.
`saturationExtension_fullRecognitionPairs_pullback` then compares `g`'s
pair-system map on any recognized pair `V, W` with the existing
`hf.fullRecognitionPullback hc V W hl`. It uses compatibility with target
restriction from the recognized image to `W`.

`saturationExtension_fullRecognitionPairs_represents` transfers the existing
full-test universal property along this map equality. Thus the actual
pair-system map represents the literal relative image
`W.chart ⁻¹' (f.baseMap '' V.locus)` whenever the image of `V` lies in `W`.

## Bounded equivalences and finite étaleness

The selected definition, `saturationExtension_fullRecognitionPairEquiv`,
assumes that this relative image is the whole target spectrum. It applies
`Represents.univEquiv` to obtain a bounded algebra equivalence from
`W.algebra` to `V.algebra`.
`saturationExtension_fullRecognitionPairEquiv_toBoundedAlgHom` proves that
its forward bounded map is exactly `g.fullRecognitionPairs.pullback V W h`.

`saturationExtension_isFiniteEtale` proves `g.IsFiniteEtale` with domain
`Set.univ`. For each recognized target subset `W`, choose the constructed
`generalReverseRecognizedImage hc W`. Its locus is `f.baseMap ⁻¹' W.locus`.
The homeomorphism underlying `hf` is surjective, so the image of this locus
is all of `W.locus`; the relative image is therefore the whole spectrum.
The bounded equivalence above identifies the actual pair-system pullback.
Its bounded inverse supplies the controlled lifts required by
`BoundedAlgHom.isFiniteBanach_of_lift`, and its underlying algebra
bijection gives `AlgebraicallyFiniteEtale.of_bijective`. These are exactly
the finite Banach and algebraic finite-étale clauses of the existing
`IsFiniteEtale` predicate.

Finally, `saturationExtension_isEtaleAllPieces` applies the Library's
`IsFiniteEtale.isEtaleAllPieces` theorem. All claims concern the actual
saturation extension and its complete bounded maps. Transport to arbitrary
localized representatives remains a separate step.

## Provenance

This is internal infrastructure derived from existing Library declarations,
not a new translation of an external theorem. The comparisons reuse
`StrongQuasiIsoDomainImage`, `GeneralQuasiIsoRecognition`,
`FullRecognitionPairSystems`, and `FullRecognitionIsomorphismCriterion`;
the final finiteness argument uses `FiniteMorphismSmallNeighborhoods` and
`FullRecognitionEtaleComposition`. The Lean proof implements the route
explained above without assuming any unproved geometric statement.
