# The residue field extension along a ring map

Module `StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an algebra `R → R'`, a prime `𝔭'` of `R'` and a prime `𝔭` of `R` with `𝔭'` lying over `𝔭`, `Ideal.residueFieldAlgebra` packages the induced field map κ(𝔭) → κ(𝔭') as an algebra structure. It is an abbreviation, not a global instance; the file makes it a local instance. `Ideal.isScalarTower_residueField` shows that the extension is a map of `R`-algebras, `IsScalarTower R κ(𝔭) κ(𝔭')`; it is a theorem, not an instance.

The module docstring and the empty section headings still announce the Noetherian descent of the fibres of a finite type algebra (Tags 053R and 00R1), base change of quotients, the comparison of fibres and descent along faithfully flat maps; none of these is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FinitePresentation/FiniteTypeDescent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 23 declarations of the source file 2 are kept. The 21 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
