# Transporting weak solutions across ring isomorphisms

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppWeakSolutionBridge`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For two base-change packages D and D′ (`IsDiscreteValuationRing.IntegralClosureBaseChange`) of extensions of discrete valuation rings with finite extensions of the base fraction fields, the file shows that being a weak solution passes along isomorphisms of the recorded rings.

- `isWeakSolution_of_ringEquiv_square`: if ring isomorphisms eA : D.A₁ ≃+* D′.A₁ and eB : D.B₁ ≃+* D′.B₁ commute with the structure maps A₁ → B₁, then D′ is a weak solution whenever D is. The two packages can start from different towers.
- `reductionRingEquiv` is the isomorphism X ⧸ nilradical X ≃+* Y ⧸ nilradical Y induced by a ring isomorphism X ≃+* Y, given by `RingEquiv.quotientNilradical`.

The proof pulls a maximal ideal of D′.B₁ back along eB and uses `ramificationIdx_map` to preserve ramification indices.

The library’s `IsWeakSolution` tests for ramification index one at all maximal ideals of the upper ring. The file proves only the forward implication; its module docstring also announces the converse, the tensor-product cancellation, the isomorphisms of integral closures and the transport for two packages over one field, which are not in the file.

References are Stacks Project Tag 09EN, Tag 09F5 and Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppWeakSolutionBridge.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 17 declarations of the source file 2 are kept. The 15 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
