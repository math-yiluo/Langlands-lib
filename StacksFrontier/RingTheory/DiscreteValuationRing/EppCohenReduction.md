# Finiteness over the intermediate DVR in Epp’s reduction

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppCohenReduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In Epp’s proof, one interposes a discrete valuation ring Λ in a tower A → Λ → B. This file proves the finiteness half of that step: B is finite over Λ when Λ is complete and the two residue fields agree.

- `module_finite_of_residueField_map_surjective` proves that an extension Λ → B of DVRs is module-finite if Λ is complete and κ_Λ → κ_B is surjective. Only Λ needs to be complete.
- `exists_sub_algebraMap_mem_maximalIdeal` restates surjectivity of κ_Λ → κ_B as B = Λ + 𝔪_B, for a local map of local rings.
- For a uniformizer π of B, `pow_maximalIdeal_restrictScalars_le_span_sup` covers 𝔪_B^i by Λ·π^i + 𝔪_B^{i+1} as Λ-modules, and `top_le_span_pow_sup_pow_maximalIdeal` iterates this: B is covered by the Λ-span of 1, π, …, π^{i-1} together with 𝔪_B^i.
- `Module.Finite.of_top_le_span_sup_quotient`: if a module is covered by the span of a finite set together with a submodule N, the quotient by N is a finite module.

The finiteness proof uses residue surjectivity to generate each successive maximal-ideal layer of B over Λ by a power of a uniformizer π. If e is the ramification index, the first e powers generate B modulo the extended maximal ideal of Λ. Krull’s intersection theorem gives separatedness, and adic finiteness gives the result.

The finiteness is one input of the reduced situation used by Tag 09F8. The module docstring also describes the formal smoothness of A → Λ and the combined statement for the tower, and lists their declarations among the main results; the file does not contain them.

References include Tag 09F9, Tag 031D for adic finiteness, and Epp’s *Elimination of wild ramification*.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppCohenReduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 5 are kept. The 2 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.formallySmoothNAdic_of_irreducible_algebraMap`, `IsDiscreteValuationRing.isWeaklyUnramified_and_formallySmoothNAdic_and_module_finite_of_tower`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 4 references to EGA and SGA that the source writes as attributes of that library belong to declarations left out; none is listed.
