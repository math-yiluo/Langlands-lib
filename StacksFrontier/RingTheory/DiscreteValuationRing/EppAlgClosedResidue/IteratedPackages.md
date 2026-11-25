# Composing weak solutions after finite base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IteratedPackages`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A reduced tensor product after finite base change can split into several field factors. This file gives conditions for combining weak solutions on the corresponding discrete valuation rings into a weak solution for the original extension.

## Results

- `reducedTensorFactorsEquiv` composes a presentation of the reduction of L ⊗[K] K₁ with a product decomposition of that presentation. If both comparisons agree with the K₁-structure maps, the result is a K₁-algebra equivalence. `reducedTensorFactorsEquiv_left` also records compatibility with L when the original presentation respects the left tensor factor.
- `isWeakSolution_of_iterated_packages` composes weak solutions for a prescribed finite base change K₂/K₁ on every field factor of the first reduced base change. It uses a compatible factor decomposition and integral DVR presentations of the factors and the intermediate base.
- `isWeakSolution_of_finite_extension_of_perfect_integralClosure_residue` preserves a weak solution from K₁ to any prescribed further finite K-extension K₂ containing K₁. It assumes both original DVRs are complete and the original base has perfect residue field. `perfectField_residueField_of_finite` supplies perfection upstairs for a module-finite local map.
- `exists_finite_extension_forall_isWeakSolution_of_perfect_residueField` combines a finite family of weak solutions for complete DVRs over a common complete DVR with perfect residue field into one finite extension. `exists_finite_extension_isWeakSolution_of_factor_solutions` applies this to all the field factors of a first base change, assuming their DVRs and the intermediate base are complete and the latter has perfect residue field.

The proof passes from the first weak solution to weakly unramified maps on its factors. Perfection persists through the finite residue extension and allows further base change on each factor. A common finite extension into which the given solution fields embed then works on the entire product by associativity of reduced base change.

The factor-solutions result takes existence of a weak solution on each factor as the hypothesis `hsol`. `isWeaklyUnramified_of_equiv` transports weak unramifiedness of DVR extensions along compatible ring equivalences.

The module docstring also announces transport along universe lifts, and a docstring compares with a lemma `isWeakSolution_of_finite_extension`; neither is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppAlgClosedResidue/IteratedPackages.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 16 declarations of the source file 8 are kept. The 8 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_finite_extension_forall_isWeakSolution`, `IsDiscreteValuationRing.exists_isWeakSolution_of_integral_ring_extension`, `IsDiscreteValuationRing.exists_isWeakSolution_of_ulift_fraction_fields`, `IsDiscreteValuationRing.isExtension_of_equiv`, `IsDiscreteValuationRing.isWeakSolution_of_finite_extension`, `IsDiscreteValuationRing.reducedTensorProductULiftLeftEquiv`, `IsDiscreteValuationRing.reducedTensorProductULiftLeftEquiv_tmul`, `IsDiscreteValuationRing.residueField_forall_exists_pow_iff_of_finite_square`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
