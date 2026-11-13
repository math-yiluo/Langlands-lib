# Henniart's route with Tate's conductor formula reduced to rank one

Worker 4803 wrote this module (Task 4803).

## Statement

`Henniart.Extension.SupercuspidalCorrespondenceHenniartRankOneInputsStatement.{uK, uW, uV}`
is the implication from the following six propositions to the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`:
1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`;
2. `NonabelianSystem.Exists.{uK, uW} K eC` for every p-adic field `K` and reciprocity
   family `eC`;
3. `NumericalSurjectivityStatement.{uK, uW, uV}`;
4. `Ramification.Padic.FiniteInertiaConductorRefinementStatement.{uK, max uK uW} K A` for
   every p-adic field `K` and every finite-dimensional complex representation `A` of
   its local Weil group with carrier universe `max uK uW`;
5. `LocalFactor.SpectralConductor.CommonClosureRankOneConductorStatement K` for every
   p-adic field `K`;
6. `Conductor.ConductorExponentStatement.{uK, uV}` (JPSS (5.1)).

The statement asserts none of its hypotheses.

## Implemented proof

`supercuspidalCorrespondenceHenniartRankOneInputs` applies the published
`supercuspidalCorrespondenceHenniartSixInputs`. Normalized reciprocity existence is the
Library theorem `LocalClassField.commonClosureReciprocityExistence`. Tate's spectral
conductor formula for each `K` is `SpectralConductor.spectralConductorRankOneReduction`
applied to premises 4 and 5 at `K`.

Compared with the six-input entry, normalized reciprocity existence is discharged, and
Tate's spectral conductor formula is replaced by premises 4 and 5. Task 5737 proves
premise 4. The ingredients of premise 5 are Tasks 5738 and 5739.
