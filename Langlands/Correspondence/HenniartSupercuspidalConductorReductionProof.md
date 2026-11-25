# Henniart's three-input route with the supercuspidal p-adic conductor premise

The theorem
`Langlands.Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`
proves exactly the published proposition
`Langlands.Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement.{uK,uW,uV}`,
at arbitrary independent field, Weil-carrier and representation universe levels.

Its only premises, in order, are

1. `CandidateExistenceStatement.{uK,uW,uV,uW,uK}`;
2. `NumericalSurjectivityStatement.{uK,uW,uV}`;
3. `Conductor.SupercuspidalPadicConductorExponentStatement.{uK,uV}`.

The conclusion is
`Correspondence.SupercuspidalCorrespondenceStatement.{uK,uW,uV}`.
This is a conditional reduction; it asserts none of these three premises.

## Imports and implemented proof

`HenniartSupercuspidalConductorReductionStatement` supplies the unchanged
published target. `HenniartSupercuspidalConductorSurjectivity` supplies the new
surjectivity-step reduction and, through its supporting finiteness module,
candidate finiteness with the restricted conductor premise. Their paired
Markdown explains those adaptations and the new generic-conductor bridge.

The remaining imports discharge exactly the same auxiliary inputs as the
published SixInputs, RankOneInputs, FiveInputs and ThreeInputs route:

- `ClassFieldTheory.Local.CommonClosureExistenceProof` supplies
  `LocalClassField.commonClosureReciprocityExistence`.
- `LocalFactor.NonabelianSystemExistsProof` supplies
  `NonabelianSystem.exists_system` for each normalized reciprocity family.
- `LocalFactor.SpectralConductorReduction` supplies
  `SpectralConductor.spectralConductorRankOneReduction`.
  Its two inputs come from
  `LocalFactor.Ramification.InertiaConductorRefinementProof`, through
  `Ramification.Padic.finiteInertiaConductorRefinement`, and
  `LocalFactor.SpectralConductorRankOneProof`, through
  `SpectralConductor.commonClosureRankOneConductor`.
- `Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof` supplies
  `RankinSelberg.equalRankEpsilonCharacterChange`.
- `Representation.RankinSelberg.PairEpsilonExponentProof` supplies
  `pairEpsilonExponentReduction`, which turns that change-of-character theorem
  into `PairEpsilonExponentStatement.{uK,uV,0}`.
- `HenniartCorrespondenceInduction` supplies
  `supercuspidalCorrespondenceHenniartInduction`. Apply it to candidate
  existence, the new surjectivity step, the new candidate-finiteness result,
  normalized reciprocity and the local-constant systems.

The spectral conductor reduction uses its existing representation universe
`max uK uW` internally; it imposes no relation between `uK`, `uW` and `uV`.
The rank-one second member in the group epsilon comparison has universe `0`,
as required by the published pair-exponent reduction.

## Provenance and scope

This is an internal adaptation of the published Henniart route, following
Henniart 2000, §4.3, and using the numerical-surjectivity premise of
Henniart 1988, Theorem 1.2. The sources and interpretations of the unchanged
target and all auxiliary theorems remain those of their published modules.
The supporting generic-conductor comparison applies the restricted JPSS
1981 (5.1) premise only to a supercuspidal representation over its canonical
p-adic field. The other route arguments use the published arithmetic
conductor, epsilon and finiteness results.

The adaptation consists of four Lean/Markdown pairs: this one,
`HenniartSupercuspidalConductorSurjectivity`, `HenniartSupercuspidalConductorFiniteness`
and `Representation.Conductor.SupercuspidalPadicGenericConductor`. It uses the target
pair, its dependencies, the p-adic field modules and the existing route modules as they
are. No full generic conductor premise or unproved JPSS generation assertion is used.
