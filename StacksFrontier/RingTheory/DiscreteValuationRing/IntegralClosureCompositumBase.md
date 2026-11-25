# Compatibility of algebra structures on a reduced base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureCompositumBase`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let O be a commutative algebra over the commutative rings R and A′, with A′ also an R-algebra. Let F and K₁ be extensions of a field K with compatible algebra maps from the rings, in particular through O to F and through A′ to K₁. Write S and A₁ for the integral closures of R and A′ in K₁, and T for the integral closure of O in the reduction of F ⊗ₖ K₁. The file identifies the two actions of S on T that occur in normalized base change.

`algebraIntegralClosureOfLocalizedBase` makes A₁ an S-algebra by the inclusion inside K₁. Its scalar towers express compatibility with R and with the embedding into K₁. The definition `algebraIntegralClosureCompositumOfBase` gives T its S-algebra structure through the right-factor map into O ⊗ᵣ S. The theorem `algebraMap_integralClosureCompositumOfBase_eq` identifies the resulting map S → T with the composite through A₁, yielding `isScalarTower_integralClosureCompositumOfBase`.

The proof computes both maps in the reduced tensor product. By `coe_algebraMap_integralClosureCompositumOfBase`, the tensor construction sends b to the class of 1 ⊗ b, with b viewed in K₁. The integral-closure map through A₁ gives the same class by its defining formula.

The compositum statements assume that S is module-finite over R and put the rings and fields in a common universe. Their algebra-map compatibility applies to a general A′ with the given towers, including the localization used in the reduced-fibre application. The scalar tower connects the normalized stalk description to the base-change solution property.

References include Tag 09EM, Tag 09EN and Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/IntegralClosureCompositumBase.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `algebraMap_integralClosureCompositumOfBase`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
