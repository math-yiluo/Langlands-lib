# Projectivity along a flat local homomorphism

Module `StacksFrontier.RingTheory.Module.LocallyFree.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`projective_iff_baseChange` proves that for a flat local homomorphism R → S of commutative local rings and a finite R-module M, M is projective over R if and only if S ⊗[R] M is projective over S. The forward direction is base change of projective modules. For the converse, a flat local homomorphism of local rings is faithfully flat, so faithful flatness descends flatness from S ⊗[R] M to M, and a finite flat module over the local ring R is free.

The module docstring still describes the ring C^∞(ℝ) of smooth functions, its quotient by the ideal of functions vanishing near zero as a finite flat module that is not projective (Remark 00NY), and a finite-projectivity form of the descent theorem; none of them is in the file, whose namespace `Stacks.FiniteFlatNotProjective` holds only section headings.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Module/LocallyFree/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 26 declarations of the source file 1 are kept. The 25 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
