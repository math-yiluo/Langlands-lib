# Ascent of Epp’s condition through finite extensions

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionAscent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The separability of perfect-core elements over a perfect base field survives a finite extension of the target field. The file applies this to residue fields to propagate Epp’s condition through towers and squares of local rings.

- `isSeparable_of_mem_perfectCore` proves that every perfect-core element of a finite field extension E/F is separable over F. For F and E of exponential characteristic p, `minpoly_coeff_mem_perfectCore_of_finite` places the coefficients of its minimal polynomial in the perfect core of F. The auxiliary root lemma keeps each pⁿ-th root of a perfect-core element in the perfect core.
- `isSeparable_of_mem_perfectCore_of_tower` takes a tower k ⊆ F ⊆ E with k perfect, E/F finite and F and E of exponential characteristic p. If every perfect-core element of F is separable over k, the same holds for E.
- `EppCondition.of_module_finite` ascends along a module-finite local map B → B′ with κ_A perfect. In a compatible square, `EppCondition.of_finite_square` also allows the base to change from A to A′, with finiteness required on the target side.
- `EppCondition.of_tower` restricts the condition for A → C to A → B in a local tower A → B → C of common target residue exponential characteristic. `perfectField_residueField_of_isIntegral` gives perfectness upstairs for an integral local map with perfect base residue field.

Taking an iterated p-th root at the finite purely inseparable exponent of E over the separable closure of F in E puts the original element in that closure. Frobenius then relates the minimal polynomials of the element and its roots. The coefficients are algebraic over k by hypothesis, so the element is algebraic over k and hence separable by perfectness.

Perfectness of κ_A is a separate hypothesis in the ascent theorems. Restriction to an intermediate ring requires neither perfectness nor finiteness. The exact equality of the base residue image with the perfect core, used in Tag 09F8, can fail after finite extension, as with the inclusion of the field of p elements into the field of p² elements. The module docstring lists a perfectness result for module-finite maps, which the file does not contain; it is the module-finite case of `perfectField_residueField_of_isIntegral`.

References include Tag 09F9 and Epp’s *Elimination of wild ramification*.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppConditionAscent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 8 are kept. The 2 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.EppCondition.forall_of_finite_square`, `Stacks.EppTheorem.perfectField_residueField_of_module_finite`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
