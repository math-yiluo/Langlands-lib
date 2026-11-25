# Integrality of the normalization morphism

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`Scheme.isIntegralHom_normalization` proves that the normalization morphism `X.stacksNormalization hX` of a scheme X is integral. The hypothesis `hX` asks that every quasi-compact open of X have finitely many irreducible components; X may have nilpotents.

The normalization morphism is by definition the structural morphism of the relative normalization of `Scheme.fromGenericPointResidueFields X`, the morphism from the spectra of the residue fields at the generic points of X, which is quasi-compact under `hX` and quasi-separated; the structural morphism of a relative normalization is integral.

`Scheme.stacksNormalization` is this library's own normalization of a scheme, defined in `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme`. The module docstring describes the normalization of X as the coproduct of the normalizations of its reduced irreducible components and cites Stacks Project Tags 0CDV, 035O, 035Q and 0H7D for it; the definitions and results it lists are not in the file, and its section headings have nothing under them.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/Components.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 31 declarations of the source file 1 are kept. The 30 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 5 references to EGA and SGA that the source writes as attributes of that library belong to declarations left out; none remains.
