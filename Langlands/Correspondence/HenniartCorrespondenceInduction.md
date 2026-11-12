# Henniart's route with the rank induction carried out

Author: Worker 4803. Module `Langlands.Correspondence.HenniartCorrespondenceInduction`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers and local constants), `uV` (supercuspidal carriers), all
independent. `stableCorrespondence_of_steps` also has an independent universe
`uE` for local-constant values.

## Statement: `SupercuspidalCorrespondenceHenniartInductionStatement.{uK, uW, uV}`

The implication

1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`,
2. `SurjectivityStepStatement.{uK, uW, uV, uW}`,
3. `SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}` (items 1–3 are
   components of Worker 14's published `HenniartStableMapStatement`: Henniart
   2000, Théorème 3.1 with §§3.7–3.8, and two parts of §4.3),
4. `LocalClassField.CommonClosureReciprocityExistence.{uK}` (normalized local
   reciprocity in a common closure),
5. `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uK, uW} K eC` (Deligne's local
   constants for every normalized family)

implies the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`: for every
prime `p` and every `F : PadicField.{uK} p` there is exactly one supercuspidal
correspondence. Each hypothesis is a published Library proposition. The
statement asserts none of them.

It is the published `SupercuspidalCorrespondenceHenniartRemainingStatement`
(module `HenniartCorrespondenceRemaining`) with its hypothesis
`StableCorrespondenceStatement.{uK, uW, uV, uW}` replaced by items 2 and 3.

## Other result

`stableCorrespondence_of_steps` proves

`RankOneStageStatement.{uK, uW, uV, uE} → ChoiceIndependenceStepStatement.{uK, uW, uV, uE} →
SurjectivityStepStatement.{uK, uW, uV, uE} → StableCorrespondenceStatement.{uK, uW, uV, uE}`.

## Provenance

Internal. Henniart (2000), §4.3, printed pp. 452–453 (PDF pp. 14–15), proves
Théorème 4.2 by induction on `n`. The case `n = 1` is clear. For `n ≥ 2`,
Henniart first proves a), the stable image, and then b). By Henniart (2000),
printed p. 453, the surjectivity in b) follows from the main result of his
reference [He 3], Henniart, *La conjecture de Langlands numérique pour GL(n)*,
Ann. Sci. École Norm. Sup. (4) 21 (1988), 497–544. The three parts are the
published statements `RankOneStageStatement`, `ChoiceIndependenceStepStatement`
and `SurjectivityStepStatement`. The first two are proved in
`HenniartRankOneStageProof.md` and `HenniartChoiceIndependenceStepProof.md`. The
surjectivity step and the finiteness of candidate sets remain as hypotheses.

## Proof

- `stableCorrespondence_of_steps` uses strong induction on `n : ℕ+`
  (`PNat.strongInductionOn`). For `n = 1` it uses the rank-one stage. For
  `n ≠ 1` it has `1 < n`. The inductive step, applied to the induction
  hypothesis, gives `StableExistsAt K n`, and the surjectivity step then gives
  `StableSurjectiveAt K n`.
- `supercuspidalCorrespondenceHenniartInduction` applies the published
  `supercuspidalCorrespondenceHenniartRemaining` with:
  - `stableCorrespondence_of_steps` for its `StableCorrespondenceStatement`
    hypothesis, with `uE := uW`;
  - `rankOneStage_of_reciprocity hCE hrec` for the rank-one stage;
  - `choiceIndependenceStep_of_inputs hCE hfinite hrec hsys` for the inductive
    step;
  - the surjectivity hypothesis for the surjectivity step.

  The other hypotheses are passed through unchanged.

Standard axioms only.
