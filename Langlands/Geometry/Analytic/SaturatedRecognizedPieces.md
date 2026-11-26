# Étaleness over all recognized pieces, stated on saturated presentations

The Library's predicate `AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces`
in `FullRecognitionEtaleComposition` is stated for a strong map
`g : StrongHom A.saturatedPresentation B.saturatedPresentation`, with original
presentations `A` and `B` as parameters. Its definition uses `A` and `B` only
through their constructed saturations: the recognized subsets of
`A.atlas.saturatedAtlas` and `B.atlas.saturatedAtlas`, the full-recognition
pair system of `g`, and the canonical map `B.localDomainToFullRecognition`.
This module restates the same definitions with an object of the saturated
category in place of each original presentation, so that the predicate no
longer mentions the index universe of an original atlas.

The field `K : Type u` is complete and ultrametric. Saturated presentations
have ambient spaces and chart indices in one universe `v`. No Hausdorff or
compactness assumption is imposed.

## Definitions

- `AffinoidAtlasPresentation.recognitionInclusion T` is the strong map from a
  presentation `T` (chart indices in the universe of its space) to its
  recognition presentation `T.recognitionPresentation`, on the identity of the
  space. Its pullback from a recognized subset `V` to an original chart `S`
  inside `V` is the original restriction of `V` to `S`. The data and proofs
  are those of `localDomainToFullRecognition`, with the atlas `T.atlas` in
  place of `A.atlas.saturatedAtlas`.
- For saturated presentations `A` and `B` and
  `g : StrongHom A.presentation B.presentation`,
  `toRecognitionTarget g` is the saturated composite of `g` with
  `B.presentation.recognitionInclusion`, and `recognitionPairs g` is its
  recognized source extension: the admissible pair system on all pairs of
  recognized subsets of the source and target atlases.
- `IsFiniteOverPieces g V U`, `HasRecognizedPiecesAt Q g y`,
  `IsFlatOnRecognizedPiecesAt`, `IsUnramifiedOnRecognizedPiecesAt`,
  `IsEtaleOnRecognizedPiecesAt` and `IsEtaleOnRecognizedPieces` are the
  definitions `IsFiniteOver`, `HasAllPiecesAt`, `IsFlatAtAllPieces`,
  `IsUnramifiedAtAllPieces`, `IsEtaleAtAllPieces` and `IsEtaleAllPieces`
  with the recognized subsets of `A.presentation.atlas` and
  `B.presentation.atlas` and with the pair system `recognitionPairs g`.

## Comparison with the existing predicate

For original presentations `A` and `B` in any universes `u`, `v`, `w`:

- `recognitionInclusion_saturatedPresentation` states
  `A.saturatedPresentation.recognitionInclusion =
  A.localDomainToFullRecognition`;
- `StrongHom.recognitionPairs_ofSaturation` states that `recognitionPairs`
  on `ofSaturation A` and `ofSaturation B` is `g.fullRecognitionPairs`;
- `StrongHom.isEtaleAllPieces_iff_isEtaleOnRecognizedPieces` states
  `g.IsEtaleAllPieces ↔ IsEtaleOnRecognizedPieces g`, the latter for
  `ofSaturation A` and `ofSaturation B`.

All three are proved by `rfl`: after unfolding, both sides are the same terms.

## Provenance

The restated definitions are those of `FullRecognitionFiniteMorphisms` and
`FullRecognitionEtaleComposition`, which transcribe Berkovich, *Étale
cohomology for non-Archimedean analytic spaces* (1993): finite morphisms
(Lemma 1.3.7 and the following definition), Proposition 3.2.3(b),
Definition 3.2.5, and Definition 3.3.4 with Proposition 3.3.7. The quoted
passages and their page locators are in `FullRecognitionFiniteMorphisms.md`
and `FullRecognitionEtaleComposition.md`. The restatement itself is internal:
it changes only which Lean object carries the saturated atlas, and the three
comparisons above show that no condition is added or removed.
