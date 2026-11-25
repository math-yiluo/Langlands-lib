# Finite residue support and compatible fraction fields

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.FiniteSupportAbsorption`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file keeps track of fraction fields when a finite weakly unramified extension absorbs residue coefficients for Epp’s prime-degree reductions, through a shared normal residue extension for an entire family.

`EppCondition.exists_fractionField_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield` takes a complete DVR R with perfect residue field and a finite family of local R-algebras satisfying Epp’s condition. For finite sets in their residue perfect cores and depth N, it gives a finite weakly unramified complete R₂/R with perfect Galois residue extension and its finite fraction-field extension. In every compatible common residue overfield, each specified coefficient has a pᴺ-th root from the residue field of R₂.

The proof adds the fraction field of R₂ to the output of the existing residue absorption; a private lemma gives the compatible finite extension of fraction fields for a module-finite faithful extension of a DVR. R, R₂ and their fraction fields share one universe.

The module docstring also announces fraction-field towers for embedded DVR maps and finite-support and mixed-level absorption steps, which the file does not contain.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppPrimeDegree/FiniteSupportAbsorption.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 2 are kept. The 4 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.EppCondition.absorb_finiteSupport_or`, `Stacks.EppTheorem.EppCondition.absorb_mixedLevelSupport_or`, `Stacks.EppTheorem.EppCondition.exists_fractionField_finiteEtale_absorbs_finset`, `Stacks.EppTheorem.exists_fractionField_algebra_tower`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
