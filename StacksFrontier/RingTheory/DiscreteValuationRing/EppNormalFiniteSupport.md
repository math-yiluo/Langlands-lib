# Finite normal extensions containing conjugate coefficients

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppNormalFiniteSupport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves the field-theoretic facts that let one normal extension supply chosen coefficients or their power roots across the field factors of a base change.

For a normal extension N/k and a common overfield Ω over k, `mem_fieldRange_of_normal_of_minpoly_eq` places a k-integral x in Ω in the image of N whenever some y in N has the same minimal polynomial. `finset_maps_mem_fieldRange_of_normal` applies this to a finite subset of another extension K/k. Its hypothesis `hrep` supplies integrality and a matching minimal polynomial in N for each coefficient, and its conclusion holds for any compatible embeddings of K and N in Ω.

`exists_pow_eq_algebraMap_of_normal` transfers a given pᵈ-th root r from K into the image of N when r is integral over k and its minimal polynomial has a representative in N. `finset_exists_pow_eq_algebraMap_of_normal` does this for every element of a finite set, given paired root witnesses.

The proofs use that a representative’s minimal polynomial splits in N. N and the witnesses are inputs; a docstring cites a construction of N that the file does not contain.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppNormalFiniteSupport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.exists_normal_finite_minpoly_representatives`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
