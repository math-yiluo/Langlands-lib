# Laurent coefficients over the base

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.TameConstantNumerator`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves the normalization step of the branch of Epp’s argument in which all Laurent coefficients belong to perfect cores: once their p^N-th roots come from one base residue field, the Laurent parameters of every factor are base fractions up to integral terms.

- `laurent_expansion_map` maps a Laurent expansion ξ = ∑ₖ σₖ t^{-(N-k)} + b over B ⊆ L through a compatible square B → S, L → E, sending the coefficients and the integral term through B → S. With the private `residue_mk_algebraMap_sigma`, `exists_transported_constant_laurent_data` carries an expansion, its coefficient lifts, and their truncated ring homomorphism to a factor along compatible local and fraction-field maps, keeping the coefficient roots and their comparison with the roots from the base.
- Given root equalities in the new residue fields and compatible lifts modulo the Nth powers of the maximal ideals, `exists_forall_coeffLift_sub_algebraMap_mem_pow_of_residueField` replaces each coefficient lift by a base element modulo that power, in characteristic p, for a whole family at once.
- `exists_forall_base_parameter_add_integral_of_constant_laurent` uses these congruences for weakly unramified extensions R → Sᵢ of discrete valuation rings in characteristic p, with K the fraction field of R. For Laurent expansions in the image of a base uniformizer, it expresses each parameter as the image of a base fraction plus an integral term.

The family normalization applies a one-coefficient normalization theorem at each coefficient and chooses the base elements by finite choice. In the last theorem the image of the base uniformizer is a uniformizer of each factor, by weak unramifiedness, so the congruences hold modulo its Nth power and the principal part differs from a base fraction by an integral element.

The roots from the base residue field and their comparison `hrootBase` in each factor are hypotheses; the file does not produce them. Its output is the parameter decomposition used as input to the Artin–Schreier solver. The module docstring also announces a shared tame Kummer extension and the input preparation for residue absorption, which the file does not contain; the two sections meant for them are empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedFactorSync/TameConstantNumerator.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 5 are kept. The 9 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.exists_coeffSupport_forall_mem_perfectCore`, `Stacks.EppTheorem.exists_forall_baseLift_pow_eq`, `Stacks.EppTheorem.exists_forall_coeffLift_sub_algebraMap_mem_pow`, `Stacks.EppTheorem.exists_forall_rootBase_pow_eq`, `Stacks.EppTheorem.exists_residueField_lift_mod_pow_map`, `Stacks.EppTheorem.exists_sharedExtension_factorSolutions_of_tame`, `Stacks.EppTheorem.forall_pow_eq_of_wild_eq_empty`, `Stacks.EppTheorem.laurent_numerator_eq_algebraMap`, `Stacks.EppTheorem.sum_sub_sum_mem_of_forall_sub_mem`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
