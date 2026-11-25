# Tensor associativity and flatness in a scalar tower

Module `StacksFrontier.RingTheory.Flat.TowerLTensor`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let C be a commutative algebra over a commutative ring A and let D and P be C-modules with compatible A-actions. Tensor associativity transfers flatness over A between P and the tensor product D ⊗ P over C.

`TensorProduct.AlgebraTensorModule.assoc_comp_lTensor` proves naturality in the A-module X of the associator from (D ⊗₍C₎ P) ⊗₍A₎ X to D ⊗₍C₎ (P ⊗₍A₎ X). The lemma `TensorProduct.AlgebraTensorModule.lTensor_baseChange_injective_iff` then equates injectivity of the map induced by an A-linear map u on these two tensor products.

`Module.Flat.tensorProduct_of_flat_left` proves A-flatness of D ⊗₍C₎ P when P is A-flat and D is C-flat. `Module.Flat.of_tensorProduct_of_faithfullyFlat` recovers A-flatness of P from that of D ⊗₍C₎ P when D is faithfully flat over C, by reflection of injectivity under tensoring.

Stacks Project, Tag 0584.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/TowerLTensor.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
