# The module colimit condition after extension of scalars

Module `StacksFrontier.RingTheory.FinitePresentation.ModuleDescent.ModuleColimit`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file formulates the module colimit condition after extension of scalars.

In `Stacks.FinitePresentation.ColimitDescent`, take `A`-algebras `R_i` indexed by a preorder, maps `φ` between them for `i ≤ j` and maps `ψ i : R_i → S` to an `A`-algebra `S`. The `A`-linear maps `transMod` and `canonMod` tensor these ring maps with the identity on an `A`-module `P`; `transMod_tmul` and `canonMod_tmul` give their values on pure tensors. The library's `IsModuleColimit` records that the canonical maps to `S ⊗[A] P` are jointly surjective, and that elements of the same stage with equal images become equal at a later stage (its fields `jointly_surjective` and `exists_eq_of_canonMod_eq`).

No identity, composition or compatibility condition is imposed on `φ` and `ψ`, and the file proves no case of `IsModuleColimit`. The module docstring still lists the descent of equality of maps out of a finite module (Tag 05LI, part (1)) and a cokernel criterion for surjectivity after base change; neither is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FinitePresentation/ModuleDescent/ModuleColimit.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 20 declarations of the source file 8 are kept. The 12 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 6 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
