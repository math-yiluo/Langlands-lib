# Weak solutions after totally ramified base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TotallyRamifiedTensor`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a tower of discrete valuation rings A → B → C with fraction fields K → L → M, this file transports a weak solution for the base-changed tower back to A → C. The base change is a finite separable extension K₁/K totally ramified with respect to A.

- `exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct_of_perfectResidue` obtains a finite extension F/K whose integral-closure base change for A → C is a weak solution. The input has A and B complete, A → B weakly unramified, M/L finite, and the residue field of A perfect of prime characteristic p. The hypothesis `hnext` is a recursive solution: for the integral closures A₁, B₁ and C₁ of A, B and C in K₁, L ⊗[K] K₁ and M ⊗[K] K₁, it supplies a weak solution over A₁ → C₁ as soon as A₁ → B₁ is weakly unramified.
- `exists_extensionLevel_mem_Ico` gives a nonempty set of level numerators and a rational extension level in [0, p) for a finite-level degree-p extension M/L over the fraction field of a DVR B. It uses the specified cyclotomic map into B and the association of its element `wElt f` with π raised to the positive exponent e₁, for irreducible π.

The descent proof constructs the integral closures A₁, B₁ and C₁ and uses total ramification to identify the residue fields compatibly and preserve weak unramifiedness. It then applies the iterated weak-solution theorem with just one factor. The level bound applies the earlier least-level theorem after transporting the finite-level data through `ULift`.

The descent statement also takes the field hypotheses `hL₁` and `hM₁` on L ⊗[K] K₁ and M ⊗[K] K₁ and the finiteness of the latter over the former, `hfinite`. All rings and fields in the public statements are in one universe.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppAlgClosedResidue/TotallyRamifiedTensor.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_totallyRamified_tensorProduct`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
