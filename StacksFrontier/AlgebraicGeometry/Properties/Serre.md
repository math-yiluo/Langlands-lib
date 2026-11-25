# Depth of a local ring along its maximal ideal

Module `StacksFrontier.AlgebraicGeometry.Properties.Serre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one lemma. For a local ring A with maximal ideal 𝔪, `depth_eq_depthSup_of_isLocalRing` says that the depth of A along 𝔪, `Module.stacksDepth A 𝔪 A`, equals `Module.depthSup A 𝔪 A`, the supremum of the lengths of the A-regular sequences in 𝔪. The depth is ⊤ by definition when 𝔪 · A = A; since 𝔪 is a proper ideal this case does not occur, and what remains is the same supremum.

The module docstring describes Serre’s conditions (Rₖ) and (Sₖ) for schemes and the criteria for reducedness and normality (Tags 033Q, 0344 and 0345); none of these definitions or results is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/Serre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 1 are kept. The 23 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
