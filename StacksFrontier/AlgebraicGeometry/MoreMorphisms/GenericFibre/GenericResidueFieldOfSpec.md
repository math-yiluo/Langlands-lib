# The residue field at the generic point of an affine scheme

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a domain R, the residue field at the generic point of Spec R is a fraction field of R under the canonical map from global sections.

- `isIso_residue_genericPoint` identifies the generic stalk of any integral scheme with its residue field, since the stalk is already a field.
- `specResidueFieldAlgebra` gives the R-algebra structure on κ(x) for any point x of Spec R by evaluation. It is supplied locally in the fraction field statements.
- `specResidueFieldAlgebra_eq`: for a domain R, at the generic point this structure map is the map into the function field followed by the residue map.
- `isFractionRing_specResidueField_genericPoint` transports the fraction field property of the generic stalk across the residue map.

The fraction field identification supplies part of Step D of Tag 0559.

## Watch for

- The module docstring also lists a version for a point given by an equality to the generic point, and the fact that an injective map of domains carries generic point to generic point on spectra (a hypothesis of Tag 0552); the file holds neither.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/GenericFibre/GenericResidueFieldOfSpec.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 4 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isFractionRing_specResidueField`, `AlgebraicGeometry.map_genericPoint_Spec_map`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
