# One orbit extension for a family of wild degree-p layers

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppWildFamilyPreparation`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In equal characteristic p, the file prepares Laurent presentations of Artin–Schreier layers and obtains weak solutions for a finite family over a single extension of the base fraction field. Wild support is measured relative to the perfect core of each layer's intermediate residue field.

- `exists_prepared_wild_laurent_of_charP` takes a weakly unramified extension of discrete valuation rings A → B, a degree-p Galois extension M/L of the fraction field of B, and a uniformizer π of A. Under `hram`, which excludes integral Artin–Schreier parameters for generators of M/L, it produces a presentation in π of minimal positive pole order n. It supplies a residue section and a compatible ring homomorphism `liftMod` into B modulo the nth power of its maximal ideal. Among coefficient positions outside the perfect core, the pole orders are pairwise unrelated by powers of p, and every coefficient has a root at a finite Frobenius depth that admits no further pth root. All other coefficients have roots at every depth.
- `exists_shared_orbitExtension_forall_isWeakSolution_of_prepared_wild_laurent` takes such prepared data over a common A and π, with varying towers A → Bᵢ → Cᵢ and fraction fields K, Lᵢ and Mᵢ. With nonempty wild support at every member, it produces one finite Galois extension E/K, totally ramified with respect to A and of degree p raised to a common rank, with a weak solution for every A → Cᵢ over E.
- `exists_finite_extension_isWeakSolution_or_constant_laurent_of_charP` applies preparation to a single such tower under the degree-p Galois and `hram` hypotheses. It returns either a finite weak solution or a minimal positive Laurent presentation with all coefficients in the perfect core.

The proof removes collisions of wild pole orders by changing the Artin–Schreier generator. Shared orbit parameters make the largest scaled wild pole unique at each member. Taking roots at the common rank off the wild support leaves those poles at most n, so the same maximum controls the full Laurent range and the prepared mixed-Laurent theorem applies at each member.

The family premise `hJ` requires a nonempty wild set for every member. The all-perfect-core branch is returned as data for a separate argument, and integral parameters fall outside `hram`. The single-layer disjunction places all rings and fields in one universe.

References are Stacks Project Tag 09F0, clause (A), Tag 09F1 and Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppWildFamilyPreparation.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
