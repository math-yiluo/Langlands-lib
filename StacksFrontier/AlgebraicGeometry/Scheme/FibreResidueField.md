# Residue fields along a morphism surjective on stalks

Module `StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one lemma. For a morphism of schemes i : Z ⟶ X that is surjective on stalks and a point z of Z, `AlgebraicGeometry.surjective_residueFieldMap_of_surjectiveOnStalks` says that the induced map of residue fields κ(i(z)) → κ(z), `i.residueFieldMap z`, is surjective. The proof composes the surjective stalk map with the surjective residue map of Z and uses their compatibility with the residue field map.

The module docstring describes a comparison of transcendence degrees of residue fields on a scheme-theoretic fibre, citing Tags 01J9 and 04NM; that comparison is not in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Scheme/FibreResidueField.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 1 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.trdeg_residueField_comp_of_surjectiveOnStalks`, `AlgebraicGeometry.trdeg_residueField_fiber`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
