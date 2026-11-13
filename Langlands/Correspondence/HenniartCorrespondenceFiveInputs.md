# Henniart's route with refinement invariance of conductors discharged

Worker 4803 wrote this module (Task 4803). It imports
`Langlands.Correspondence.HenniartCorrespondenceRankOneInputs`,
`Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof` and
`Langlands.LocalFactor.Ramification.InertiaConductorProfile`.
The profile module retains the general two-field conductor comparison; the
refinement proof module supplies the shared entry theorem.

## Statement

`Henniart.Extension.SupercuspidalCorrespondenceHenniartFiveInputsStatement.{uK, uW, uV}`
is the implication from the following five propositions to the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`:
1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`;
2. `NonabelianSystem.Exists.{uK, uW} K eC` for every p-adic field `K` and reciprocity
   family `eC`;
3. `NumericalSurjectivityStatement.{uK, uW, uV}`;
4. `LocalFactor.SpectralConductor.CommonClosureRankOneConductorStatement K` for every
   p-adic field `K`;
5. `Conductor.ConductorExponentStatement.{uK, uV}` (JPSS (5.1)).

These are premises 1, 2, 3, 5 and 6 of the published
`SupercuspidalCorrespondenceHenniartRankOneInputsStatement`, in the same order and at the
same universe levels. Premise 4 of that statement, refinement invariance of presentation
conductors (`Ramification.Padic.FiniteInertiaConductorRefinementStatement.{uK, max uK uW} K A`
for every p-adic field `K` and every finite-dimensional complex representation `A` of its
local Weil group with carrier universe `max uK uW`), is no longer a hypothesis.

The statement asserts none of its hypotheses.

## Implemented proof

`supercuspidalCorrespondenceHenniartFiveInputs` applies the published
`supercuspidalCorrespondenceHenniartRankOneInputs` to the five hypotheses and supplies its
premise 4 as `fun p _ K A => Ramification.Padic.finiteInertiaConductorRefinement K A`.

`Ramification.Padic.finiteInertiaConductorRefinement` is proved in the new module
`Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof` (see its Markdown). It
has the type that Task 5737 asks for, at independent universe levels for the field and the
carrier; here it is used at field universe `uK` and carrier universe `max uK uW`.

## Provenance

This is a derived reduction: it composes a published Library reduction with a new
theorem and invokes no new literature result. The sources of the remaining five inputs and of
the target are documented with the respective Library statements. On 13 November 2026 the
open inputs had these TaskHub proof tasks: input 1, Task 5583; input 2, Task 4913; input 3,
Task 5584; input 4, Task 5815; input 5, Task 5032.
