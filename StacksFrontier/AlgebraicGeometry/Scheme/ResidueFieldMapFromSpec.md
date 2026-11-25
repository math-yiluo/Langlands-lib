# Isomorphisms on residue fields

Module `StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Surjectivity on a stalk implies that the induced map on residue fields is an isomorphism.

For a morphism of schemes f : X ⟶ Y and a point x of X at which the stalk map is surjective, `isIso_residueFieldMap_of_stalkMap_surjective` says that `f.residueFieldMap x` is an isomorphism. The proof passes surjectivity to the quotients by the maximal ideals and uses injectivity of field maps; the public theorem restates a private lemma with the same statement.

The module docstring announces the isomorphism for the canonical morphism `Spec κ(x) ⟶ X` and an identification of residue fields at the closed point of the spectrum of a local ring; neither is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Scheme/ResidueFieldMapFromSpec.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 2 are kept. The 3 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isIso_residueFieldMap_fromSpecResidueField`, `AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section`, `AlgebraicGeometry.isIso_residueFieldMap_of_surjective_stalkClosedPointTo`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
