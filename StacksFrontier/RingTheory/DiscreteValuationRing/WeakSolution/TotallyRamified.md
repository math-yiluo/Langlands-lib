# Totally ramified base change of discrete valuation rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolution.TotallyRamified`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A ⟶ B be an injective local map of discrete valuation rings with compatible fraction fields K ⟶ L. A finite separable extension K₁/K that is totally ramified with respect to A preserves weak unramifiedness under base change.

`isDiscreteValuationRing_integralClosure_of_totallyRamified` shows that the integral closure A₁ of A in such an extension is a discrete valuation ring. If the maximal ideal of A extends to the maximal ideal of B, `isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified` shows that L₁ = L ⊗[K] K₁ is a field and B₁ = B ⊗[A] A₁ is a discrete valuation ring. The map A₁ ⟶ B₁ is injective and extends the maximal ideal of A₁ to that of B₁. The theorem also gives a B-algebra equivalence of B₁ with the integral closure of B in L₁. It identifies the two embeddings of A₁ in L₁ and transfers the maximal-ideal equality to the integral closure, which has fraction field L₁.

The proof uses uniqueness of the maximal ideal and the Dedekind property for A₁. Residue degree one identifies the quotient of B₁ by the extended maximal ideal with the residue field of B. The tensor product is local, and flatness makes the image of an A₁-uniformizer a nonzerodivisor. Localizing at its powers gives the fraction field, and integral closedness identifies B₁ with the integral closure.

The weak unramifiedness hypothesis `hweak` is the ideal equality itself. The total ramification hypothesis `htot` is expressed by `IsTotallyRamifiedWithRespectTo`, from which the proof uses the unique maximal ideal above that of A and residue degree one.

The base change theorem is Tag 09ER. The result for A₁ is recorded as a special case of SGA 6 X 7.16.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09ER](https://stacks.math.columbia.edu/tag/09ER) | `isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 6 X 7.16 | `isDiscreteValuationRing_integralClosure_of_totallyRamified` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/WeakSolution/TotallyRamified.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
