# Minimal polynomials of perfect-core elements

Module `StacksFrontier.FieldTheory.PerfectCoreSeparable`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file descends minimal polynomials to the perfect core.

For E/F of prime characteristic p, `minpoly_coeff_mem_perfectCore_of_forall_isSeparable` places the coefficients of the minimal polynomial over F of a core element of E in the core of F. The hypothesis `hsep` requires separability over F only on the core of E. The iterated roots of a core element stay in the core, so Frobenius comparison of their minimal polynomials applies. `exists_monic_separable_map_eq_minpoly_of_forall_isSeparable` lifts the polynomial to a monic separable polynomial over the core of F.

The module docstring also announces a separability criterion for a field generated over L by an embedded copy of a separable extension, which the file does not contain.

The file cites Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/PerfectCoreSeparable.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 2 are kept. The 1 left out are not needed by the results for which the extract is made: `isSeparable_of_adjoin_range_of_isSeparable`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
