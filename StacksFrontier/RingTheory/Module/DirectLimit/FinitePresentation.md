# Base change of modules to a directed colimit of algebras

Module `StacksFrontier.RingTheory.Module.DirectLimit.FinitePresentation`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file shows that tensor products commute with a directed colimit of commutative algebras, in the elementwise form used for finite-stage descent. The stages Sⱼ are algebras over a common base A and are indexed by a nonempty directed preorder J; R is an A-algebra receiving compatible maps from them.

`Stacks.ColimitPresentation.FPModules.isModuleColimit` proves the elementwise colimit conditions of `Stacks.FinitePresentation.ColimitDescent.IsModuleColimit` for R ⊗[A] P and the modules Sⱼ ⊗[A] P, for any A-module P: every element of R ⊗[A] P comes from some Sⱼ ⊗[A] P, and two elements of Sⱼ ⊗[A] P with the same image in R ⊗[A] P already agree in some Sₖ ⊗[A] P with k ≥ j. Its hypotheses say that the stage maps are compatible (`hf`), every element of R comes from a stage (`hsurj`), and every stage element mapping to zero vanishes at a later stage (`hinj`).

The proof turns these hypotheses into a private A-linear equivalence between the module direct limit of the Sⱼ and R, tensors it with P, and composes with the commutation of tensor products with direct limits (`TensorProduct.directLimitLeft`); the two conditions then come from the description of the elements of a module direct limit and of when two of them are equal.

The file also holds the private equivalence `baseChangeQuotEquiv`, R ⊗[S] (N ⧸ p) ≃ (R ⊗[S] N) ⧸ p.baseChange R, which nothing in it uses.

The module docstring still announces the descent of finitely presented R-modules and of linear maps between base changes to a finite stage, under a bijectivity hypothesis `hR`, citing Tag 05N7 and Tag 05LI; these results are not in the file, where the variable `hR` and the namespace `Module` at the end are left without declarations.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Module/DirectLimit/FinitePresentation.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 10 are kept. The 8 left out are not needed by the results for which the extract is made: `Module.exists_finitePresentation_and_baseChange_eq_of_lift_bijective`, `Stacks.ColimitPresentation.FPModules.algebraLift_of`, `Stacks.ColimitPresentation.FPModules.baseChangeQuotSpanEquiv`, `Stacks.ColimitPresentation.FPModules.exists_algebraMap_eq`, `Stacks.ColimitPresentation.FPModules.exists_finitePresentation`, `Stacks.ColimitPresentation.FPModules.exists_forall_algebraMap_eq`, `Stacks.ColimitPresentation.FPModules.exists_map_eq_zero`, `Stacks.ColimitPresentation.FPModules.solution`.
- 7 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
