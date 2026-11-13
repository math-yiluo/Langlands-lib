# Henniart's route with local constants and rank-one conductor transport discharged

Worker 4803 wrote this module (Task 4803). It imports
`Langlands.Correspondence.HenniartCorrespondenceFiveInputs`,
`Langlands.LocalFactor.NonabelianSystemExistsProof` and
`Langlands.LocalFactor.SpectralConductorRankOneProof`.

## Statement

`Henniart.Extension.SupercuspidalCorrespondenceHenniartThreeInputsStatement.{uK, uW, uV}`
says that the following three propositions together imply the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`:
1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`;
2. `NumericalSurjectivityStatement.{uK, uW, uV}`;
3. `Conductor.ConductorExponentStatement.{uK, uV}` (JPSS (5.1)).

These are premises 1, 3 and 5 of the published
`SupercuspidalCorrespondenceHenniartFiveInputsStatement`, in the same order and at the
same universe levels. Two premises of that statement are no longer hypotheses:
- premise 2, `NonabelianSystem.Exists.{uK, uW} K eC` for every prime `p`, p-adic field
  `K` and reciprocity family `eC`;
- premise 4, `LocalFactor.SpectralConductor.CommonClosureRankOneConductorStatement K` for
  every prime `p` and p-adic field `K`.

The statement does not assert any of its three hypotheses.

## Implemented proof

`supercuspidalCorrespondenceHenniartThreeInputs` applies the published
`supercuspidalCorrespondenceHenniartFiveInputs` to the three hypotheses and supplies the
two others from published proofs:
- premise 2 as `fun p _ K eC => NonabelianSystem.exists_system K eC`. The published
  theorem `LocalFactor.NonabelianSystem.exists_system` (module
  `Langlands.LocalFactor.NonabelianSystemExistsProof`) proves
  `NonabelianSystem.Exists.{uF, uV} F e` for every p-adic field `F` and every
  reciprocity family `e`, at independent universes. Here it is used at `uF = uK`,
  `uV = uW`.
- premise 4 as `SpectralConductor.commonClosureRankOneConductor`. The published
  theorem (module `Langlands.LocalFactor.SpectralConductorRankOneProof`) has exactly
  the type of premise 4, at field universe `uK`.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

This is a derived reduction. It composes a published Library reduction with two
published theorems and introduces no new literature result. The Library statements
document the sources of the target and of the remaining three inputs. On 13 November 2026
the open inputs had these TaskHub proof tasks: input 1, Task 5583; input 2, Task 5584;
input 3, Task 5032.
