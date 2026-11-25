# Smoothness through open stabilizers

The module `Langlands.Representation.Smooth.OpenStabilizer` characterizes smooth representations
of a topological group by the openness of the stabilizers of vectors.

## Content

- `isSmooth_iff_forall_isOpen`: for a representation `ρ` of a topological group `G` on a complex
  vector space, `Langlands.IsSmooth ρ` (every vector is fixed by an open subgroup) holds exactly when
  `{g | ρ g v = v}` is open for every `v`. The stabilizer of `v` is a subgroup (private
  `stabilizerSubgroup`); it is open when it contains an open subgroup
  (`Subgroup.isOpen_mono`), and it is itself an open subgroup fixing `v` when it is open.

The Library's `isSmoothVector_iff_isOpen_stabilizer`
(`Langlands/Representation/Smooth/Transfer/StabilizerProof.lean`) states the same through Mathlib's
`Representation.stabilizer`, whose module the Library's subject files avoid; this file needs
neither. It is used for the smoothness of Kudla's representation
(`Langlands/Theta/DualPair/Unitary/Splitting.lean`), whose source states smoothness as the openness of
stabilizers.

## Relation to the source

The statement replaces the source's definitions `PRep.IsSmooth` and `SplitWeil.IsSmoothRep`
(<https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`,
`src/Development/AbelianVarietyTheory/Definitions/Foundations/MatrixMeasurableSpace.lean`, lines
15–16) by the Library's notion. The proof is that of the private
`isSmooth_iff_forall_isOpen` of `Langlands/Theta/Heisenberg/StoneVonNeumann.lean`, made public here
in a general file.

## Declarations

- `Langlands.isSmooth_iff_forall_isOpen`

## Dependencies

`Langlands.Representation.Smooth.Definitions`; Mathlib: `Topology.Algebra.OpenSubgroup`,
`Analysis.Complex.Basic`.
