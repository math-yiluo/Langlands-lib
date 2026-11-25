# Polynomiality of the Hilbert function of a homogeneous quotient

Module `StacksFrontier.RingTheory.HilbertFunction.DegreeBound`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a polynomial ring in d variables with the standard grading over a field k, the Hilbert function of a homogeneous quotient is eventually polynomial.

## Results

An admissible graded module in d variables is the library's own structure `AdmissibleGradedModule`: a module over the polynomial ring in d variables over k, finitely generated over it, with an internal ℕ-grading by finite-dimensional k-subspaces in which each variable raises degree by one.

- `exists_cokernel_admissible` constructs the cokernel of multiplication by the last variable on an admissible module in d + 1 variables as an admissible module in d variables. For n ≥ 1 its Hilbert value is the dimension of the original degree-n piece minus the rank of multiplication from degree n − 1. With the existing kernel construction, `exists_kernel_cokernel_firstDifference` gives H(n) − H(n − 1) = H_C(n) − H_K(n − 1) for n ≥ 1, where C and K are the cokernel and kernel.
- `isNumericalPolynomialByNaturalArgs_hilb` proves numerical polynomiality for every admissible graded module by induction on d. The quotient by a homogeneous ideal is admissible by `exists_admissible_of_ideal`. `isNumericalPolynomialByNaturalArgs_hilbertFunction` gives numerical polynomiality of its Hilbert function on natural arguments, and `isNumericalPolynomialByNaturalArgs_hilbertFunction_sub` gives it for the first difference.

For the induction, the zero-variable Hilbert function eventually vanishes, and rank–nullity makes the first difference numerical by the induction hypothesis. The antidifference theorem then gives polynomiality.

Polynomiality permits the zero ideal; the ideal must be homogeneous (`hI_hom`). The module docstring still announces the degree bound of Tag 00K3, and the section headed “Main results” at the end of the file is empty: the bound is not in the file.

References include Tag 00JZ for numerical polynomials and first differences.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertFunction/DegreeBound.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 11 are kept. The 3 left out are not needed by the results for which the extract is made: `Stacks.HilbertFunction.PolynomialQuotient.hilbertFunction_degree_lt`, `Stacks.HilbertFunction.PolynomialQuotient.hilbertFunction_eventually_zero_of_dim_one`, `Stacks.HilbertFunction.PolynomialQuotient.isNumericalPolynomial_hilbertFunction`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
