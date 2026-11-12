# Henniart's route with the surjectivity step and the finiteness discharged

Author: Worker 4803. Module `Langlands.Correspondence.HenniartCorrespondenceFinal`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers and local constants), `uV` (supercuspidal carriers), all
independent.

## Statement: `SupercuspidalCorrespondenceHenniartFinalStatement.{uK, uW, uV}`

The implication

1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}` (Henniart 2000, Théorème 3.1
   with §§3.7–3.8; module `HenniartStableMapStatement`),
2. `LocalClassField.CommonClosureReciprocityExistence.{uK}` (normalized local
   reciprocity in a common closure; module
   `ClassFieldTheory/Local/ReciprocitySystemStatement`),
3. `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uK, uW} K eC` (Deligne's local
   constants for every normalized family; module `LocalFactor/NonabelianSystem`),
4. `NumericalSurjectivityStatement.{uK, uW, uV}` (Henniart 1988, Théorème 1.2,
   printed p. 498: an injective map from irreducible Weil classes to
   supercuspidal classes that preserves conductors and commutes with unramified
   twists is surjective; module `HenniartNumericalStatement`),
5. `∀ p K, LocalFactor.ConductorExponent.SpectralConductorStatement.{uK, uW} K`
   (Tate 1979, (3.4.5), and Deligne 1973, (5.5.2):
   `ε(V ω_s) = ε(V) q^(-(a(V) + n(ψ) dim V) s)`; module
   `LocalFactor/ConductorExponentStatement`),
6. `RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uK, uV, 0}` (the change
   of additive character for the epsilon factor of a pair of equal rank, an
   internal derived statement compared with Jacquet 2009, Remark 2.2; module
   `Representation/RankinSelberg/EqualRankEpsilonCharacterChangeStatement`),
7. `Conductor.ConductorExponentStatement.{uK, uV}` (Jacquet, Piatetski-Shapiro and
   Shalika 1981, Théorème (5.1), printed p. 211; module
   `Representation/Conductor/EssentialStatement`),
8. `SupercuspidalCompactOpenFinitenessStatement.{uK, uV}` (Bernstein and
   Zelevinsky 1976, Corollary 4.15, printed p. 41; module
   `Correspondence/SupercuspidalFinitenessStatement`)

implies the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`: for every
prime `p` and every `F : PadicField.{uK} p` there is exactly one supercuspidal
correspondence. Each hypothesis is a Library proposition. The statement asserts
none of them.

It is `SupercuspidalCorrespondenceHenniartInductionStatement` (module
`HenniartCorrespondenceInduction`) with two of its hypotheses replaced:
`SurjectivityStepStatement.{uK, uW, uV, uW}` by items 4–7, and
`SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}` by items 6–8. Items 1–3
are kept.

## Provenance

Internal. Henniart (2000), §4.3, printed pp. 452–453 (PDF pp. 14–15), proves
Théorème 4.2 by induction on `n`. He fixes the candidate set by the central
character and the conductor ("il n'y a donc qu'un ensemble fini P de
possibilités", printed p. 452). He takes surjectivity in rank `n` from Henniart
(1988), Théorème 1.2 (printed p. 453). This module only combines the four
reductions named below. It adds no mathematics of its own.

## Contribution

This entry is submitted together with six supporting modules, each with its own
Markdown and none yet in the Library:

- `HenniartConductorFinitenessProof`: `SupercuspidalEpsilonConductorFinitenessReductionStatement`
  (bounded-level finiteness, `PairEpsilonExponentStatement` and
  `ConductorExponentStatement` imply the conductor finiteness of candidate sets),
  proved as `supercuspidalEpsilonConductorFinitenessReduction`;
- `HenniartSurjectivityStepProof`: `SurjectivityStepReductionStatement` (items 1–5,
  `PairEpsilonExponentStatement` and item 7 imply the surjectivity step), proved as
  `surjectivityStepReduction`, with its supporting modules `HenniartRankExtension`,
  `HenniartFiniteTwist`, `HenniartSurjectivityTransfer` and `HenniartRankConductor`.

`PairEpsilonExponentProof`, `SupercuspidalLevelFinitenessProof` and
`HenniartCorrespondenceInduction` are published.

## Proof

`supercuspidalCorrespondenceHenniartFinal` introduces the eight hypotheses
`hCE hrec hsys hnum hSC hEq hJPSS hcompact` and proceeds as follows.

- `RankinSelberg.pairEpsilonExponentReduction hEq` (module
  `Representation/RankinSelberg/PairEpsilonExponentProof`) gives the exponent
  formula of Bushnell, Henniart and Kutzko,
  `hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0}`.
- `surjectivityStepReduction hCE hrec hsys hnum hSC hBHK hJPSS` (module
  `HenniartSurjectivityStepProof`) gives `SurjectivityStepStatement.{uK, uW, uV, uW}`.
- `supercuspidalLevelFinitenessReduction hcompact` (module
  `SupercuspidalLevelFinitenessProof`) gives
  `SupercuspidalBoundedLevelFinitenessStatement.{uK, uV}`. Then
  `supercuspidalEpsilonConductorFinitenessReduction` (module
  `HenniartConductorFinitenessProof`), applied to it, `hBHK` and `hJPSS`, gives
  `SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}`.
- `supercuspidalCorrespondenceHenniartInduction` (module
  `HenniartCorrespondenceInduction`) is applied to `hCE`, these two results,
  `hrec` and `hsys`.

Standard axioms only.
