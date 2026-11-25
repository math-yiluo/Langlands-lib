# Conditions (1) and (2) for smoothness at a point

Module `StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of schemes f : X ⟶ S and a point x of X, this file defines the first two of the six conditions of the pointwise smoothness criterion of Tag 01V9, as propositions in the namespace `Stacks.SmoothAtJacobian`.

1. `Condition1` asks that f be smooth at x in the sense of `InfinitesimalLifting.SmoothAt`, that is, smooth on an open neighbourhood of x.
2. `Condition2` asks that the stalk map be flat and the fibre through x be smooth, in the same sense, at its corresponding point over κ(f(x)).

The file proves nothing about them, and the definitions carry no hypothesis; the equivalence of Tag 01V9 assumes local finite presentation. The module docstring describes all six conditions, the cotangent spaces used for the numerical conditions and the list collecting the conditions; only the two definitions above are in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/SmoothAtJacobian/Conditions.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 19 declarations of the source file 2 are kept. The 17 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
