# Henniart's route with local converse, twist independence and the unramified-twist law proved

Author: Worker 4803. Module `Langlands.Correspondence.HenniartCorrespondenceRemaining`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers and local constants), `uV` (supercuspidal carriers), all
independent.

## Statement: `SupercuspidalCorrespondenceHenniartRemainingStatement.{uK, uW, uV}`

The implication

1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`,
2. `StableCorrespondenceStatement.{uK, uW, uV, uW}` (items 1 and 2 are
   components of Worker 14's published `HenniartStableMapStatement`: Henniart
   2000, Théorème 3.1 with §§3.7–3.8, and Théorème 4.2),
3. `LocalClassField.CommonClosureReciprocityExistence.{uK}` (normalized local
   reciprocity in a common closure),
4. `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uK, uW} K eC` (Deligne's local
   constants for every normalized family)

implies the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`: for every
prime `p` and every `F : PadicField.{uK} p` there is exactly one supercuspidal
correspondence. Each hypothesis is a published Library proposition. The
statement asserts none of them.

The hypotheses are those of `SupercuspidalCorrespondenceHenniartReducedStatement`
(module `HenniartCorrespondenceReduction`), in the same order, without three of
them:

- `RankinSelberg.SupercuspidalLocalConverseStatement.{uK, uV, uV}` (first);
- `UnramifiedTwistIndependenceStatement.{uK, uW, uV, uW}` (fourth);
- `RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV}` (last).

## Provenance

Internal. It is Henniart's reduction (Henniart 2000, §4.4, printed p. 453,
PDF p. 15, with Henniart 1993, §4) with three more hypotheses proved:

- The local converse theorem, the Corollary of Henniart 1993, printed p. 340.
  Other workers proved it in the Library (`SupercuspidalLocalConverseProof.md`).
- Unramified-twist independence of stable images: Henniart 2000, §4.4, with
  Henniart 1993, §4.3, printed p. 349. It is proved from candidate existence
  and local reciprocity in `HenniartTwistIndependenceProof.md`.
- The unramified-twist law of pair epsilon factors: Henniart 1993, §4.4,
  printed p. 349. Its sources are recorded in `UnramifiedTwistStatement.md` and
  `UnramifiedTwistEpsilonProof.md`.

## Proof

`supercuspidalCorrespondenceHenniartRemaining` applies
`supercuspidalCorrespondenceHenniartReduced` with:

- the published `RankinSelberg.supercuspidalLocalConverse` (module
  `SupercuspidalLocalConverseProof`) as its first hypothesis;
- `unramifiedTwistIndependence_of_reciprocity hCE hrec` (module
  `HenniartTwistIndependenceProof`) as its fourth;
- `RankinSelberg.unramifiedTwistEpsilon` (module `UnramifiedTwistEpsilonProof`)
  as its seventh.

The other hypotheses are passed through unchanged. Standard axioms only.
