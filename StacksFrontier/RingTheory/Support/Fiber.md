# Support of a tensor product base change

Module `StacksFrontier.RingTheory.Support.Fiber`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`Module.support_tensorProduct_eq_preimage_comap`: for a ring map R → S and a finite R-module M, the support of S ⊗_R M over S is the inverse image of the support of M under the map Spec S → Spec R. It is the case of the tensor product, with the map m ↦ 1 ⊗ m, of `IsBaseChange.support_eq_preimage_comap` from `StacksFrontier.RingTheory.Support.Basic`.

The module docstring describes the support of a fibre module over the fibre ring κ(r) ⊗_R S, the fibre support in Spec S and its local dimension along an integral extension, none of which is in the file.

The theorem is Tag 0BUR for the tensor model of a base change; the file also refers to Tag 00L1 for support.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Support/Fiber.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 22 declarations of the source file 1 are kept. The 21 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
