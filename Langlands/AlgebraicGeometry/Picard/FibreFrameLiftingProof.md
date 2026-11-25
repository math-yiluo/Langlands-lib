# Local fibre frame lifting detected by two closed restrictions: proof

The target is split into two prerequisite statements. The first is proved by the published proof
`restrictionPerfectModels`. The second prerequisite is the published
proof `fibreH0RestrictionSpread`, an exact-target wrapper. It restates
the published theorem `FibreH0Spread.fibreH0RestrictionSpread`,
whose row-minor lemma adapts a private lemma of
`Langlands.LinearAlgebra.ResidueFieldMatrixSplitProof` (see `FibreH0RestrictionSpread/Split.md`).

Module `Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingProof` proves

`theorem Langlands.AlgebraicGeometry.Picard.fibreFrameLifting : FibreFrameLiftingStatement.{u}`

for the published statement `FibreFrameLiftingStatement` (module
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement`, imported unchanged). No
`sorry` and no new axioms. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

The proof is one application:

`FibreFrameLifting.fibreFrameLifting_of_models Modules.restrictionPerfectModels
  Cohomology.ModuleComplex.fibreH0RestrictionSpread`.

- `FibreFrameLifting.fibreFrameLifting_of_models (h1 : RestrictionPerfectModelsStatement.{u})
  (h2 : ModuleComplex.FibreH0RestrictionSpreadStatement.{u}) : FibreFrameLiftingStatement.{u}`
  is the conditional assembly in module
  `Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.Assembly`. It shrinks to an affine
  neighbourhood of the point, uses `h1` to get perfect models compatible with base change and
  with the two restrictions, uses `h2` to spread the degree-zero restriction isomorphism from
  the fibre to a basic open neighbourhood, lifts the frame of the first closed piece to a
  section, and tests that section on the fibre. Its steps and helper modules (`Squares`,
  `Geometry`, `DerivedHomology`, `Sections`, `FibreIso`, `Core`, `Frame`) are described in
  `FibreFrameLifting/Assembly.md` and the paired notes of the helpers.
- `Modules.restrictionPerfectModels : RestrictionPerfectModelsStatement.{u}` is in module
  `Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsProof`.
- `Cohomology.ModuleComplex.fibreH0RestrictionSpread :
  ModuleComplex.FibreH0RestrictionSpreadStatement.{u}` is in module
  `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadProof`. It is defined as
  `FibreH0Spread.fibreH0RestrictionSpread`, proved in module
  `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Main` with helper modules
  `Split` (splitting a pair of maps of finite free modules that is jointly injective over a
  field), `Homology` (homology of complexes with vanishing differentials), `Core` (the
  spreading argument for finite free complexes over one ring) and `Model` (finite free models
  over a localization and transport along homotopy equivalences). See
  `FibreH0RestrictionSpread/Main.md`.

## Modules of this proof

New modules, each with a paired Markdown note:

- `Langlands/AlgebraicGeometry/Picard/FibreFrameLiftingProof.lean` (this module);
- `Langlands/AlgebraicGeometry/Picard/FibreFrameLifting/{Squares, Geometry, DerivedHomology,
  Sections, FibreIso, Core, Frame, Assembly}.lean`.

Everything else used is imported from the Library unchanged, not copied:

- the statements `RestrictionPerfectModelsStatement` and
  `FibreH0RestrictionSpreadStatement`;
- `RestrictionPerfectModelsProof`, first in the Library at commit
  `c5eebf94883144ce00adc4e252995c28082f08a7`; its exact-target proof is at
  Library commit `5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`;
- `FibreH0RestrictionSpread/{Split, Homology, Core, Model, Main}`, in the Library from commit
  `5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`;
- `FibreH0RestrictionSpreadProof`, in the Library from commit
  `b22e185743f7c318f709e14e422801f4360105d5`.

## Provenance

The target is the intermediate conclusion of the proof of Stacks tag 0BF2, specialized as
explained in `FibreFrameLiftingStatement.md` (`more-morphisms.tex`, statement lines
9518–9541, proof lines 9543–9619, registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). The two prerequisite statements isolate the two
halves of the source argument: perfect models of the relative cohomology of the line bundle
that are compatible with base change and with the restrictions (first half), and the matrix
argument showing that the degree-zero restriction stays an isomorphism near the point (second
half). The differences from the source route are recorded in `FibreFrameLifting/Assembly.md`
and `FibreH0RestrictionSpread/Main.md`.
