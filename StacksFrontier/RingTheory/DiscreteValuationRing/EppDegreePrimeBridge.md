# Weak solutions across all factors of a reduced base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppDegreePrimeBridge`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a DVR extension A → B with fraction fields K → L and a finite extension K₁/K, the reduction of L ⊗[K] K₁ decomposes into field factors. This file assembles weak solutions from those factors.

- `reducedTensorPiEquivOfRight` turns a K-algebra decomposition into a K₁-algebra decomposition if it carries the right tensor-factor scalars to their specified images componentwise.
- `exists_finite_extension_isWeakSolution_of_reducedFactorSolutions` takes a compatible finite decomposition and complete DVRs Sᵢ presenting the field factors, integral over B and extending R. The base R must be a complete DVR integral over A, with fraction field K₁ and perfect residue field. Given a finite weak solution for each R → Sᵢ, it gives one finite extension of K solving A → B. `exists_finite_extension_isWeakSolution_of_forall_reducedFactorSolutions` obtains the decomposition internally and takes the factor rings and their solutions from `hfactors`.

The assembly uses the common-overfield theorem for the individual weak solutions.

The assumptions `hsol` and `hfactors` supply weak solutions at every factor, with `hfactors` stated for any compatible decomposition of the specified form. The comments relate this requirement to the failure of descent at a single embedding in clause (3) of Tag 09ET. In the theorem that obtains the decomposition internally, K₁ and R lie in the universe of K, and the factor fields and rings lie in the larger of the universes of K and L. The module docstring also lists a synchronized form over one shared second extension, which the file does not contain.

References include Tag 09EN, Tag 09F8 and Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppDegreePrimeBridge.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 4 are kept. The 2 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_finite_normal_baseChange_forall_reducedFactor_mem_fieldRange`, `IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
