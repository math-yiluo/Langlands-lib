# Weak solutions on all factors of a reduced tensor product

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.FactorSolutions`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension of discrete valuation rings A → B with B henselian, the file states the per-factor obligations of the all-factor route to a weak Epp solution, and proves that over a complete base with perfect residue field it suffices to solve each factor separately. The factors come from a compatible decomposition of the reduction of L ⊗[K] K₁ into fields Eᵢ finite over L, the hypotheses `hleft` and `hright` matching it with the two tensor inclusions. The base R is a discrete valuation ring integral over A with fraction field K₁.

- `algebraMap_reducedFactor_base_eq` shows that the two maps A → L → Eᵢ and A → K₁ → Eᵢ agree, because the tensor inclusions are K-algebra maps and A acts through K. `algebraMap_reducedFactor_base_eq_of_tower` gives the same through B, and the private `isScalarTower_of_reducedFactor_square` turns it into a scalar tower A → R → Eᵢ.
- `FactorSolutions` asks for a weak solution of R → Sᵢ over a prescribed finite extension K₂ of K₁ for every i, with Sᵢ the integral closure of B in Eᵢ. `IndividualFactorSolutions` allows a finite extension of K₁ chosen separately for each factor.
- `exists_finite_extension_isWeakSolution_of_forall_individualFactorSolutions` assumes R and B complete, the residue field of R perfect, K the fraction field of A, K₁/K finite, compatibility `hA` of the maps from A into K₁, and `hsol`, which gives `IndividualFactorSolutions` for every compatible decomposition. It produces a weak solution for A → B over one finite extension of K.

The proof hands the integral closures Sᵢ, with their structures and completeness, to the perfect-residue combiner, which embeds the factorwise solutions in a finite common overfield.

Both definitions quantify over every factor of the decomposition. The file states `FactorSolutions` but proves nothing about it: the module docstring also announces its tame, carried and mixed discharges and a route from it to a weak solution, which the file does not contain.

The comments cite Tag 09ET for the all-factor reduction.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedFactorSync/FactorSolutions.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 6 are kept. The 5 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.exists_reducedFactorPackages`, `Stacks.EppTheorem.factorSolutions_of_forall_isWeaklyUnramified_or_tame`, `Stacks.EppTheorem.factorSolutions_of_isWeaklyUnramified`, `Stacks.EppTheorem.factorSolutions_of_tame`, `Stacks.EppTheorem.isWeakSolution_of_forall_factorSolutions`.
- 5 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
