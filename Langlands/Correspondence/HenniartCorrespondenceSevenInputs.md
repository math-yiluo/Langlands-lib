# Henniart's route with the equal-rank change of character discharged

Author: Worker 4803. Module `Langlands.Correspondence.HenniartCorrespondenceSevenInputs`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers and local constants), `uV` (supercuspidal carriers), all
independent.

## Statement: `SupercuspidalCorrespondenceHenniartSevenInputsStatement.{uK, uW, uV}`

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
6. `Conductor.ConductorExponentStatement.{uK, uV}` (Jacquet, Piatetski-Shapiro and
   Shalika 1981, Théorème (5.1), printed p. 211; module
   `Representation/Conductor/EssentialStatement`),
7. `SupercuspidalCompactOpenFinitenessStatement.{uK, uV}` (Bernstein and
   Zelevinsky 1976, Corollary 4.15, printed p. 41; module
   `Correspondence/SupercuspidalFinitenessStatement`)

implies the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`: for every
prime `p` and every `F : PadicField.{uK} p` there is exactly one supercuspidal
correspondence. Each hypothesis is a Library proposition. The statement asserts
none of them.

It is `SupercuspidalCorrespondenceHenniartFinalStatement` (module
`HenniartCorrespondenceFinal`) without its sixth hypothesis,
`RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uK, uV, 0}`. The other
seven hypotheses are unchanged and in the same order.

## Provenance

Internal. Henniart (2000), §4.3, printed pp. 452–453 (PDF pp. 14–15), proves
Théorème 4.2 by induction on `n`. The route from the seven inputs to the target
is the one described in `HenniartCorrespondenceFinal.md`. The removed hypothesis
is the equal-rank change of additive character for pair epsilon factors. It is an
internal derived statement whose Markdown compares it with Jacquet (2009),
Remark 2.2, printed pp. 7–8. This module adds no mathematics of its own. The new
mathematics of this contribution is the proof of that hypothesis in the
supporting module.

## Contribution

This entry is submitted together with one supporting module, which has its own
Markdown and is not yet in the Library:

- `Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof`:
  the theorem `RankinSelberg.equalRankEpsilonCharacterChange` proves the Library
  proposition `RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uF, uV, uW}`
  at arbitrary independent universe levels, with no further hypotheses. Its
  Markdown describes the proof and maps it to the six derivation obligations of
  `EqualRankEpsilonCharacterChangeStatement.md`.

## Proof

`supercuspidalCorrespondenceHenniartSevenInputs` takes the seven hypotheses
`hCE hrec hsys hnum hSC hJPSS hcompact` and applies
`supercuspidalCorrespondenceHenniartFinal` (module `HenniartCorrespondenceFinal`)
to them. For the missing sixth argument it passes
`RankinSelberg.equalRankEpsilonCharacterChange.{uK, uV, 0}`. Standard axioms only.
