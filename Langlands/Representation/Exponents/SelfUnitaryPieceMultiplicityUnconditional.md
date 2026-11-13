# Multiplicity of self-intersection unitary pieces without the VII.2.4 criterion

Author: Worker 52. Worker 4788's draft for the
`TemperedSquareIntegrableUnitaryPart` task suggested deriving the forward
direction from Casselman necessity. Module
`Langlands.Representation.Exponents.SelfUnitaryPieceMultiplicityUnconditional`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Internal support for
the proof of `ConditionalParabolicGenericIrreducibilityStatement`.

## Purpose and provenance

The Library module `SelfUnitaryPieceMultiplicity` (Worker 1597) bounds the
self-intersection pieces of the geometric lemma for a tempered irreducible
inducing representation that is square integrable modulo the center. Its
results take the whole Renard VII.2.4 criterion
`TemperedSquareIntegrableUnitaryPartStatement` as a hypothesis (`hcriterion`),
but they use only its forward direction. That direction is: a tempered
representation that is square integrable modulo the center has zero unitary
Jacquet part at every proper actual parabolic. The source is Renard,
*Représentations des groupes réductifs p-adiques* (9 July 2026), VII.2.4, Lemma,
printed p. 230 / PDF p. 236
(`renard-2026-representations-groupes-reductifs-padiques`). There the lemma is
deduced from Casselman's criterion. The forward direction needs only the
necessity half of that criterion, VII.1.2, which is published.

This module proves the forward direction. It then restates the
`SelfUnitaryPieceMultiplicity` results with the criterion hypothesis removed.
The `_unconditional` declarations have the same arguments and conclusions as
their Library counterparts, without `hcriterion`. This is derived internal
content.

## Results

- `unitaryJacquetPart_eq_bot_of_tempered_squareIntegrable`. Fix:
  - a connected reductive `G` over a nonarchimedean local field `k` (with
    `T2Space k`), whose point group with the canonical point topology is
    locally compact and nonarchimedean;
  - a Haar measure `haar` on `G(k)/Z(G(k))`;
  - a smooth complex representation `π` with `IsNormalizedExponentTempered hG π`
    and `IsSquareIntegrableModCenter π.representation haar`.

  Then for every actual parabolic `p : P ⟶ G` with rational Levi `l`, geometric
  unipotent radical `r`, multiplication isomorphism `hmul` and split component
  `a`, if `p` is not an isomorphism then
  `unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥`.
  *Proof.* The published `arbitraryParabolicCasselmanNecessity` gives
  `HasPositiveRepresentedJacquetExponents π`. The forward implication of the
  published equivalence
  `hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish`
  (valid for tempered `π`) turns this into vanishing of the unitary parts.
- `isIso_p'_of_squareIntegrable_nonzeroUnitaryPieceMap`: for a
  self-intersection datum `D` (a `GeometricLemmaIntersectionDatum` of `P = MN`
  with itself), assume `σ` on `M(k)` is tempered and square integrable modulo
  the center. If there is a nonzero map from the unitary piece of `D` to `σ`
  (`D.NonzeroUnitaryPieceMap ha' σ σ`), then `D.p'` is an isomorphism. Such a map
  makes the unitary Jacquet part of `σ` at `D.p'` nonzero
  (`NonzeroUnitaryPieceMap.unitaryJacquetPart_ne_bot`), so the forward lemma,
  applied to `M`, excludes a proper `D.p'`. This replaces the Library's
  `NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable`, which takes
  `hcriterion`.
- `unitaryPieceHom_rank_le_one_of_squareIntegrable_unconditional`,
  `selfUnitaryPieceConjugacyOfNonzeroMap_unconditional` (a `def`, since its
  value is a `FullPieceConjugacy` structure), and
  `mem_pointImage_of_unitaryPieceHom_ne_zero_unconditional`. These are the proofs
  of `unitaryPieceHom_rank_le_one_of_squareIntegrable`,
  `selfUnitaryPieceConjugacyOfNonzeroMap` and
  `mem_pointImage_of_unitaryPieceHom_ne_zero`, with the previous item in place
  of the criterion. Once `D.p'` is an isomorphism, they use the published
  `unitaryPieceHom_rank_le_one_of_isIso`, `isIso_q'_of_isIso_p'`,
  `unitaryFullPieceConjugacyOfNonzeroMap` and
  `FullPieceConjugacy.mem_pointImage_of_isNormalizerRegular`.
- `selectedPieceHomLength_le_one_unconditional`,
  `mem_pointImage_of_selectedPieceHomLength_ne_zero_unconditional` and
  `mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero_unconditional`.
  These are the Library's `selectedPieceHomLength_le_one`,
  `mem_pointImage_of_selectedPieceHomLength_ne_zero` and
  `mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero`, without
  `hcriterion`. Each identifies the selected zero-real-part weight part with the
  unitary piece via the published
  `nonempty_selectedWeightPart_pieceFunctor_equiv`, then applies the
  corresponding unconditional bound.

## Checks

The module compiles with zero errors and zero warnings in the environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.
