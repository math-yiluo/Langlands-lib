# Recognized finite preimages from effective target-local descent

This internal module is the recognition step of the target-locality
development. Take a family refinement `F` of a recognized target affinoid
`W` (see `FullRecognitionFiniteTargetRefinement` and
`FullRecognitionFiniteTargetChartBinding`). Assume two further inputs:

- Hausdorffness of the literal preimage `V ∩ g⁻¹(W.locus)`, as an instance
  argument;
- an effective realization `P` of the finite algebra descent datum
  `F.models.algebraDescentData`.

From these, the module builds an actual recognized subset of the original
saturated source atlas with locus `V ∩ g⁻¹(W.locus)`. It proves that the
actual full-recognition pair pullback over `W` is finite Banach. Both
inputs are hypotheses, and this module does not prove that they exist.

## Separation by a finite recognized cover

`RecognizedSubset.hom_ext_of_finiteCover` lets two bounded maps into the
algebra of a recognized subset `V` be compared chart by chart. Suppose
finitely many recognized subsets `Y k ⊆ V.locus` cover `V.locus`. If two
maps agree after the original restriction to every original chart lying in
some `Y k`, they are equal. The proof turns the `Y k` into a finite
full-domain cover of the whole spectrum of `V`. It uses `Y k`'s own
original-chart separation (`RecognizedSubset.hom_ext`) and the full-domain
cover's algebra separation.

## Loci and Hausdorffness

`iUnion_range_modelChart` shows the model chart ranges cover exactly
`V ∩ g⁻¹(W.locus)`. Hence `chartBinding_locus_eq`: the gluing locus of the
chart binding is this literal preimage. `chartBinding_t2` transfers the
Hausdorff hypothesis to it.

## Canonical target maps

`canonicalPullback_eq`: the canonical target map of refinement chart `k`
is the original restriction of the family member `target k` to the chart
`index k`. The proof has three steps.

1. Through the identity pair system, the pair pullback is the recognized
   restriction to `target k`.
2. In the thin local-domain category, the domain recognition equivalence
   composed with the chart's structural map is the recognized restriction
   to `W`.
3. Cancelling the representing structural map (`Represents.hom_ext`)
   shows that the inverse equivalence is the original restriction of the
   recognized domain.

## Restricting a model to an original chart

Let `s` be an original saturated source chart whose range lies in
`range (modelChart k)`.

- `modelRestriction k s hs` is the bounded restriction from the `k`-th
  model algebra to the algebra of `s`. It is the thin local-domain
  inclusion of the original local domain of `s` into `modelDomain k`.
- `modelRestriction_leftMap`: after the model's left map, it is the
  original restriction of `left k` to `s`.
- `modelRestriction_rightMap`: after the model's right map, it is the
  original pair pullback `g.pullback s (index k)`. The proof cancels the
  representing canonical target map and combines the model's commutative
  square, `modelRestriction_leftMap`, the Library's
  `originalRestriction_comp_fullRecognitionPairs` and
  `canonicalPullback_eq`.
- `modelRestriction_eq`: model restriction also factors through
  `modelEquiv k`, the saturated restriction to the canonical saturated
  representative of `s`, and the comparison back to `s`. This is
  naturality of `localDomainSaturatedEquiv` together with thinness.

## The recognized preimage and its finite pullback

These declarations assume the Hausdorff instance and the effective
realization `P`.

- `recognizedPreimage P` is the recognized subset of the recognized source
  atlas obtained from the chart binding and `P` (Library
  `ChartBinding.recognizedSubset`). Its locus is `V ∩ g⁻¹(W.locus)`
  (`recognizedPreimage_locus`). `recognitionEquiv P` is the bounded
  equivalence of `P`'s algebra with it.
- `finiteBaseMap P` is `P`'s structural map from `W.algebra` transported
  by that equivalence. It is finite Banach (`finiteBaseMap_isFiniteBanach`),
  because `P`'s structural map is finite and bounded equivalences are
  finite. `finiteBaseMap_originalRestriction` shows that on each model
  chart it is `modelEquiv k` after the model's right leg after the cover
  restriction. This combines the Library's realization identity
  `originalRestriction_comp_recognitionEquiv` with `P`'s local structural
  identities.
- `preimage P` is the corresponding recognized subset of the original
  saturated atlas `A.atlas.saturatedAtlas`, obtained by recognition
  idempotence (`fullRecognitionIdempotenceIndex`).
  `preimage_locus` gives its locus `V ∩ g⁻¹(W.locus)`, and
  `preimage_admissible` places its chart image inside `W`'s chart range.
- `preimageMap P` is `finiteBaseMap P` followed by the idempotence
  equivalence, and it is finite Banach.
- `pullback_eq`: the actual pair pullback
  `g.fullRecognitionPairs.pullback (preimage P) W _` equals
  `preimageMap P`. The proof applies `hom_ext_of_finiteCover` to the cover
  of `preimage P` by the recognized images of the model domains. Fix an
  original chart `s` inside model `k`. The Library's
  `originalRestriction_comp_fullRecognitionPairs` reduces the left side to
  `g.pullback s (index k)` after the original restriction of `W`. The right
  side unwinds through four steps:
  1. the idempotence restriction identity;
  2. naturality of original restrictions in `recognizedPreimage P`;
  3. `finiteBaseMap_originalRestriction`;
  4. `modelRestriction_eq`, then `modelRestriction_rightMap`.
- `pullback_isFiniteBanach`: this pair pullback is finite Banach.

## Provenance

This is internal infrastructure. Recognizing an effectively realized finite
descent datum inside the source atlas uses the Library's chart-binding
recognition (`ChartBinding.recognizedSubset`, `affinoidRealization`) and
full recognition idempotence. The existence of the effective realization
is the separate finite affinoid algebra descent theorem (Kiehl's theorem;
see Berkovich 1993, §1.2, Remark 1.2.1(ii)), stated in the Library as
`FiniteAffinoidAlgebraDescentStatement`. It enters only as the hypothesis
`P`.
