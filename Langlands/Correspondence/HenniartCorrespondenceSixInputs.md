# Henniart's route with Bernstein–Zelevinsky finiteness proved over p-adic fields

Author: Worker 4803. Module `Langlands.Correspondence.HenniartCorrespondenceSixInputs`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers and local constants), `uV` (supercuspidal carriers), all
independent.

## Statement: `SupercuspidalCorrespondenceHenniartSixInputsStatement.{uK, uW, uV}`

The implication

1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}` (Henniart 2000, Théorème 3.1
   with §§3.7–3.8; module `HenniartStableMapStatement`),
2. `LocalClassField.CommonClosureReciprocityExistence.{uK}` (normalized local
   reciprocity in a common closure; module
   `ClassFieldTheory/Local/ReciprocitySystemStatement`),
3. `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uK, uW} K eC` (Deligne's local
   constants for every normalized family; module `LocalFactor/NonabelianSystem`),
4. `NumericalSurjectivityStatement.{uK, uW, uV}` (Henniart 1988, Théorème 1.2,
   printed p. 498; module `HenniartNumericalStatement`),
5. `∀ p K, LocalFactor.ConductorExponent.SpectralConductorStatement.{uK, uW} K`
   (Tate 1979, (3.4.5), and Deligne 1973, (5.5.2); module
   `LocalFactor/ConductorExponentStatement`),
6. `Conductor.ConductorExponentStatement.{uK, uV}` (Jacquet, Piatetski-Shapiro and
   Shalika 1981, Théorème (5.1), printed p. 211; module
   `Representation/Conductor/EssentialStatement`)

implies the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`: for every
prime `p` and every `F : PadicField.{uK} p` there is exactly one supercuspidal
correspondence. Each hypothesis is a Library proposition. The statement asserts
none of them.

It is `SupercuspidalCorrespondenceHenniartSevenInputsStatement` (module
`HenniartCorrespondenceSevenInputs`) without its seventh hypothesis,
`Henniart.SupercuspidalCompactOpenFinitenessStatement.{uK, uV}` (Bernstein and
Zelevinsky 1976, Corollary 4.15, over every nonarchimedean local field). The other
six hypotheses are unchanged and in the same order.

## Provenance

Internal. Henniart (2000), §4.3, printed pp. 452–453 (PDF pp. 14–15), proves
Théorème 4.2 by induction on `n`. The route from the inputs to the target is the one
described in `HenniartCorrespondenceFinal.md`. That route uses Bernstein–Zelevinsky
finiteness only for the finiteness of Henniart's candidate sets, which involve only
p-adic fields. The removed hypothesis is replaced by a proof of its p-adic case
(Bernstein and Zelevinsky 1976, Corollary 4.15, printed p. 41, deduced from 3.20 b),
3.21, 3.26, 3.29 and Theorem 4.14). This module adds no mathematics of its own.

## Contribution

This entry is submitted together with two supporting modules, each with its own
Markdown and not yet in the Library:

- `Langlands.Correspondence.PadicSupercuspidalFinitenessProof`: proves
  `CompactOpenFiniteness.PadicSupercuspidalCompactOpenFinitenessStatement.{uK, uV}`,
  Bernstein–Zelevinsky Corollary 4.15 for `GL_(n+1)` over every p-adic field and
  every compact open subgroup, and its bounded-level form
  `CompactOpenFiniteness.centralLevelStratum_finite`, from published forms of BZ76
  3.20, 3.21, 3.26, 3.29 and 4.14. It does not prove the all-field Library statement
  `SupercuspidalCompactOpenFinitenessStatement` (Task 5585).
- `Langlands.Correspondence.HenniartPadicConductorFinitenessProof`: proves
  `SupercuspidalEpsilonConductorFinitenessPadicReductionStatement`, the finiteness of
  Henniart's candidate sets from the Bushnell–Henniart–Kutzko and JPSS statements
  alone.

## Proof

`supercuspidalCorrespondenceHenniartSixInputs` takes `hCE hrec hsys hnum hSC hJPSS`.
It obtains `hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0}` from the
published `RankinSelberg.pairEpsilonExponentReduction` applied to the published
theorem `RankinSelberg.equalRankEpsilonCharacterChange.{uK, uV, 0}`. Then it applies
the published `supercuspidalCorrespondenceHenniartInduction` (module
`HenniartCorrespondenceInduction`) to:

- `hCE`;
- the surjectivity step `surjectivityStepReduction hCE hrec hsys hnum hSC hBHK hJPSS`
  (module `HenniartSurjectivityStepProof`);
- the finiteness of the candidate sets
  `supercuspidalEpsilonConductorFinitenessPadicReduction hBHK hJPSS` (supporting
  module), where `supercuspidalCorrespondenceHenniartFinal` used the reduction from
  all-field compact-open finiteness;
- `hrec` and `hsys`.

This is the proof of `supercuspidalCorrespondenceHenniartFinal` with the equal-rank
input discharged and the finiteness argument replaced. Standard axioms only.
