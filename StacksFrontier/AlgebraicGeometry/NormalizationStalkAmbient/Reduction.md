# The map to the total ring of fractions of the reduction

Module `StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Reduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines one ring map: the canonical map from a commutative ring to the total ring of fractions of its reduction.

For a commutative ring A, `Stacks.NormalizationStalkAmbient.reductionFractionRingHom A` is the
map A →+* `FractionRing (A ⧸ nilradical A)` obtained by composing the quotient map by the
nilradical with the localization map. No hypothesis is made on A.

The module docstring describes an identification of the total ring of fractions of the
reduction with the product of the residue fields at the minimal primes, and of the two integral
closures of Tag 0C3B; these results are not in this file, and the names the docstring gives for
them are not declared here.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationStalkAmbient/Reduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 20 declarations of the source file 1 are kept. The 19 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
