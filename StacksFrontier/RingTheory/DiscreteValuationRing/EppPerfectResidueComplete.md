# Weak solutions over a complete perfect-residue base

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppPerfectResidueComplete`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file assembles the complete perfect-residue case of Epp’s theorem from a family recursion hypothesis.

`FamilyTowerSolvable p n` is the proposition that a finite family of DVR towers with complete base and middle rings, weakly unramified lower layers, and finite normal top layers of degree at most n has weak solutions over one finite base extension. The common base residue field is perfect of characteristic p, and each middle residue field satisfies `EppCondition` over it.

`exists_finite_extension_isWeakSolution_of_perfectField` assumes that same residue setup for a tower A ⊆ B ⊆ C with fraction fields K ⊆ L ⊆ M, with A and B complete and B weakly unramified over A, and assumes M/L finite. It produces a weak solution for A → C over a finite extension of K.

The two-ring form `exists_finite_extension_isWeakSolution_of_perfectField_of_cohenTower` treats an extension A ⊆ B with κ_A perfect of characteristic p and `hepp : EppCondition A B p`, without assuming L/K finite. It assumes an interposed DVR Λ factoring A → B, with A and Λ complete, that receives a uniformizer of A as a uniformizer (`hπΛ`) and surjects on the residue field of B (`hres`). This surjectivity gives finiteness of B over Λ, and the tower theorem applies to A ⊆ Λ ⊆ B.

Both theorems take `hfam : ∀ n, FamilyTowerSolvable p n` as a hypothesis, which the file does not prove. They place the rings and fields in one universe. Several section comments describe completion, cyclotomic, universe-descent and lifting results that the file does not contain.

References include Epp’s *Eliminating wild ramification*, Kuhlmann’s correction, Tag 09F8, Tag 09F9, Tag 09ES, Tag 031D and Tag 07NJ.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppPerfectResidueComplete.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 4 are kept. The 14 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 5 references to EGA and SGA that the source writes as attributes of that library belong to a declaration left out; none is listed.
