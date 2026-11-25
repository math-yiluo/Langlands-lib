# Locality of algebras obtained by adjoining a root

Module `StacksFrontier.RingTheory.AdjoinRoot.LocalRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a commutative local ring and B = `AdjoinRoot p` for a polynomial p over A. An irreducible reduction of p gives a maximal ideal of B over the maximal ideal of A.

`AdjoinRoot.isMaximal_map_maximalIdeal` proves maximality of the extended ideal under irreducible reduction. If p is also monic, `AdjoinRoot.isLocalRing_of_irreducible_map_residue` proves that B is local. Given locality of B and irreducible reduction, `AdjoinRoot.maximalIdeal_eq_map_maximalIdeal` identifies its maximal ideal with the extended ideal. The module docstring lists a fifth main result, on residues of elements of the maximal ideal of A, which the file does not contain.

`AdjoinRoot.isLocalHom_of_monic` shows that A → B is local assuming monicity and locality of B. For maximality, B modulo the extended ideal is identified with the residue field of A with a root of the reduction of p adjoined, which is a field because that reduction is irreducible. Monicity makes B integral over A, so every maximal ideal of B contracts to the maximal ideal of A.

EGA 0 10.3.1.4 for the local homomorphism result.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 10.3.1.4 | `isLocalHom_of_monic` | algebraic successor |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdjoinRoot/LocalRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 5 are kept. The 1 left out are not needed by the results for which the extract is made: `AdjoinRoot.residue_algebraMap_eq_zero_of_mem_maximalIdeal`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
