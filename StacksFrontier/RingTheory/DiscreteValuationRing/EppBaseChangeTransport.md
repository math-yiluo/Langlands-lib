# Transporting weak solutions to an intermediate DVR

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppBaseChangeTransport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a tower of discrete valuation rings R → A → B with compatible fraction fields k → K → L, a weak solution for R → B can be used to find one for A → B by extending scalars from k to K and choosing a field quotient.

- `exists_field_factor_isWeakSolution_of_baseChange` takes a finite extension E/k, integral-closure base-change data for R → B, and a proof `hDE` that those data give a weak solution. It produces a finite extension F/K, a surjective K-algebra map K ⊗[k] E → F, and integral-closure base-change data for A → B that give a weak solution. The map is part of the conclusion, so elements of E can be followed into F.
- `exists_finite_extension_isWeakSolution_of_baseChange` starts with existence of a finite weak solution for R → B and concludes existence of one for A → B.

The proof passes to canonical base-change data and chooses a maximal-ideal quotient of K ⊗[k] E. The quotient induces a surjection on the reduced tensor products. The source is reduced Artinian, so the surjection splits off a product factor and induces a flat surjection on integral closures. This preserves the ramification indices over the integral closure of R in E. Flatness over the integral closure of A in F then gives the required index one by divisibility.

Both theorems assume compatible DVR extensions and use a single universe for the rings and fields. The conclusion gives an existential choice of field factor even when E/k is inseparable.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppBaseChangeTransport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
