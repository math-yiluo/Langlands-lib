# A morphism invertible after pre- and postcomposition

Module `StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one lemma of category theory, in the namespace `AlgebraicGeometry`. For morphisms a : A ⟶ B, b : B ⟶ D and c : D ⟶ E of a category such that a ≫ b and b ≫ c are isomorphisms, `AlgebraicGeometry.isIso_of_isIso_comp_left_and_right` says that b is an isomorphism. The inverse of a ≫ b followed by a is a section of b, and c followed by the inverse of b ≫ c is a retraction, so b is a split epimorphism and a monomorphism.

The module docstring describes the isomorphism locus of a proper birational morphism at a normal point of the target (Tag 0BFP); none of those results is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Geometric/BirationalIsomorphismLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 1 are kept. The 17 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
