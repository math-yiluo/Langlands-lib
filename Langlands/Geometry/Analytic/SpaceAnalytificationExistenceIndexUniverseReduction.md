# Conditional existence of analytifications: étaleness input reduced to an index-universe comparison

This internal module states and proves
`SpaceAnalytificationExistenceIndexUniverseReductionStatement`. The statement is a
conditional proposition with five hypotheses. Its conclusion is the unchanged published
`SpaceAnalytificationExistenceStatement.{u}`. The module proves the implication, not the
unconditional existence theorem.

## The statement

The hypotheses are, in order:

1. A localized analytic quotient for a family of étale affine charts of a separated
   algebraic space, with jointly surjective étale chart maps and a pullback square for
   each represented pairwise intersection. This is the chart form of Conrad–Temkin,
   *Non-archimedean analytification of algebraic spaces*, Theorem 4.2.2, as in input 1 of
   `SpaceAnalytificationExistenceFiveInputReductionStatement`.
2. Morphisms to an analytic space form a sheaf on the étale site (input 2 there).
3. Étaleness is detected after precomposition with a jointly surjective étale family
   on the source (input 3 there).
4. An index-universe comparison. Let `X` and `Y` be affinoid atlas presentations with
   original atlas index universe `0`, the profile `{u, u, 0}` of `presentation K P`. Then a
   strong map `g : ofSaturation X ⟶ ofSaturation Y` that is étale over all recognized
   pieces (`StrongHom.IsEtaleAllPieces (A := X) (B := Y) g`) is `strongEtale`. The
   published `strongEtale_ofSaturation_iff` is stated for original presentations at profile
   `{u, v, v}`, where the index universe equals the space universe. The premise asks for
   its reverse implication at profile `{u, u, 0}`.
5. `LocalizedEtalePullbackStatement.{u, u} K`, which supplies a pullback along an étale
   map and the étaleness of the base-changed projection (input 5 there).

All five premises quantify over complete ultrametric normed fields `K : Type u`; premises
1 and 4 require the norm to be nontrivial. Hypotheses 1, 2, 3 and 5 are unchanged from the
five-input statement.

## The proof

Hypothesis 4 of the five-input statement is the étaleness input: for an étale algebra map
`f`, `etale (localizedHom K P Q f)`. The published `affineAnalytificationLocalizedEtaleReduction`
derives it from `AffineAnalytificationEtaleStatement.{u, u, u}` and the comparison in
hypothesis 4 above. The published theorem `affineAnalytificationEtale` proves
`AffineAnalytificationEtaleStatement` in all universes. The proof applies
`spaceAnalytificationExistenceFiveInputReduction` to hypotheses 1, 2, 3, this derived
étaleness input and hypothesis 5.

## Provenance

The statement is derived. It combines the five-input reduction with the affine étale
comparison (Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Propositions 3.2.10 and 3.3.11, in the Library's affine form) and the Library's finite-to-all
upgrade for flatness and unramifiedness. The index-universe comparison is a technical premise
of the Library's universe conventions and has no separate literature counterpart: the same
equivalence is published for equal index and space universes.
