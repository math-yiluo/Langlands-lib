# Three remaining inputs for the local anisotropic affine diagram

`Langlands.Geometry.Building.localAnisotropicAffineDiagram_of_remaining_building_inputs`
proves the exact published
`Langlands.GroupScheme.LocalAnisotropicAffineDiagramStatement.{u}`
from three explicit statement hypotheses, all at the same arbitrary universe:

- `SpecialTorusExistenceStatement.{u}`;
- `QuasiSplitIndivisibleDerivativeLiftsStatement.{u}`;
- `UnramifiedSpecialApartmentChamberStatement.{u}`.

It applies the published five-input theorem
`localAnisotropicAffineDiagram_of_building_inputs`, using the published exact
proofs `quasiSplitDerivativeAffineRoots` and
`Langlands.GroupScheme.relativeRootSystemIrreducible` for its derivative and
irreducibility inputs. The other three inputs remain hypotheses. This is a
conditional supporting module; it does not prove the unconditional statement
or any of those three statements.

The noncomputable definition
`localAnisotropicAffineDiagramMatrixOfRemainingBuildingInputs` specializes
`localAnisotropicAffineDiagramMatrixOfBuildingInputs` by supplying the same
two proofs. It returns the same matrix on `Option d.Vertex`. Its specification
is the corresponding specialization of the published specification: the
matrix has the actual absolute block `d.cartan`, diagonal entries two,
nonpositive off-diagonal entries, a symmetric zero pattern, a strictly positive
integral vector in its left kernel, and vertex transitivity by permutations
preserving every entry. The definition retains every field and group
hypothesis of `LocalAnisotropicAffineDiagramStatement`, including all field and residue characteristics.

This module is an internal specialization of published interfaces. It adds no
source transcription or mathematical assertion beyond those compositions.
The construction and its absolute maximality step are explained in
[LocalAnisotropicAffineDiagramReduction](LocalAnisotropicAffineDiagramReduction.md).
The two supplied exact proofs are explained in
[QuasiSplitDerivativeAffineRootsProof](QuasiSplitDerivativeAffineRootsProof.md)
and
[RelativeRootSystemIrreducibleProof](../../GroupScheme/Rational/RelativeRootSystemIrreducibleProof.md).
No local type-A classification, local rank-one classification or local
Kneser–Tits result is used.
