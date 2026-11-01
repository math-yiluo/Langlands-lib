# Local fibre frame lifting detected by two closed restrictions: proof

Authors: Worker 1119 wrote the conditional assembly (`FibreFrameLifting.*`) and this module.
Worker 950 split the target into the two prerequisite statements and wrote the published proof
`restrictionPerfectModels` of the first prerequisite. The second prerequisite is the published
proof `fibreH0RestrictionSpread`, an exact-target wrapper written by Worker 1098. It restates
the published theorem `FibreH0Spread.fibreH0RestrictionSpread` (Workers 1119, 606 and 950),
whose row-minor lemma adapts a proof by Worker 606 (see `FibreH0RestrictionSpread/Split.md`).

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
- `RestrictionPerfectModelsProof`. Worker 950 wrote it, and it was first published (Library
  commit `c5eebf94883144ce00adc4e252995c28082f08a7`) with definition record
  `e9f50221-b816-4b25-b8bb-37dc184b044f`. Its exact-target proof record is
  `e3a70491-f7d9-4045-8948-cb64cb1a7d0d` (task `bd06d237-4ff8-40dc-b9bc-5adaf95c69b1`,
  Library commit `5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`);
- `FibreH0RestrictionSpread/{Split, Homology, Core, Model, Main}`. These were published with
  definition record `d3ec70f2-bf1d-4851-b887-5e31238f37f8` (Library commit
  `5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`), with coauthors Workers 1119, 606 and 950;
- `FibreH0RestrictionSpreadProof`, written by Worker 1098, with exact-target proof record
  `8cf7283a-ce90-4dc6-bd1a-1d6f8e5ab302` (task `f23aee47-9535-4aaf-8260-75479ca275e5`, Library
  commit `b22e185743f7c318f709e14e422801f4360105d5`).

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

This candidate replaces the rejected candidate `7d0bed38-9962-4731-9d53-eb1a8462abeb`
(review receipt `b7edf499-8745-4deb-b02c-56e411c898c5`). That review found no mathematical
defect. It required that the `FibreH0RestrictionSpread` modules, with Worker 606's credit,
first be published as a separate prerequisite. They now are. The assembly modules
`FibreFrameLifting/*` match the rejected candidate except for the note correction in
`Frame.md`.
