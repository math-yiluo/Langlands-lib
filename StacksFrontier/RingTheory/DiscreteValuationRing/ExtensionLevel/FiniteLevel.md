# Obtaining finite level after totally ramified base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.FiniteLevel`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a tower of discrete valuation rings A → B → C with fraction fields K → L → M, the file proves the finite-level step of the mixed-characteristic ramification argument. It assumes characteristic zero for K, residue characteristic p for A, weakly unramified A → B, a cyclotomic map f supplying a primitive pth root of unity in B, and Galois M/L of prime degree p.

- `exists_totallyRamified_galoisExtension_isWeakSolution_or_finiteLevel` supplies a finite extension K₁/K totally ramified with respect to A. Either it gives a weak solution for A → C, or both tensor products L ⊗ₖ K₁ and M ⊗ₖ K₁ are fields. In the latter case, the integral closure of B in the first tensor product is a discrete valuation ring with that fraction field, and the new degree-p layer has finite level for the base-changed cyclotomic quotient polynomial. When a nontrivial base change is needed, K₁ adjoins a pth root of a uniformizer of A.
- `isDiscreteValuationRing_integralClosure_of_pow_eq_unit_mul_zpow` gives a discrete valuation ring as the integral closure in a degree-p extension containing a pth root of uπⁿ when u is a unit, π a uniformizer and p does not divide the integer n. Bézout's identity changes the root to a pth root of an associate of π.

The proof writes a Kummer generator as a pth root of uπⁿ. If p divides n, rescaling reduces the parameter to a unit over the original field. Otherwise K₁ supplies t with tᵖ = π, and rescaling gives the unit parameter u in the tensor product. For a tensor field, a pth power residue gives finite level and the other residues give weak unramifiedness. The nonfield tensor case uses the separate Kummer weak-solution lemma.

Despite its name, the theorem does not assert that K₁/K is Galois: its docstring presents it as Tag 09F4 without that assertion and refers to a complete statement that is not in this file. Its conclusion allows K₁ = K, including when A → C is already weakly unramified. Both public results use a common universe for the rings and fields.

The file cites Stacks Project Tag 09F4.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ExtensionLevel/FiniteLevel.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 32 declarations of the source file 29 are kept. The 3 left out are not needed by the results for which the extract is made: `Stacks.DegreePExtensionLevel.exists_natCast_eq_unit_mul_pow_of_irreducible`, `Stacks.DegreePExtensionLevel.exists_pow_eq_unit_mul_tensorProduct_of_pow_eq_mul`, `Stacks.DegreePExtensionLevel.exists_totallyRamified_isGalois_isWeakSolution_or_finiteLevel`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
