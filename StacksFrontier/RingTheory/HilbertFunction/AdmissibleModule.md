# Numerical first differences and admissible graded modules

Module `StacksFrontier.RingTheory.HilbertFunction.AdmissibleModule`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file develops numerical polynomials on natural arguments and constructs the graded kernel needed for induction on the number of variables in a polynomial ring over a field.

- In `Stacks.HilbertFunction.PolynomialQuotient`, `IsNumericalPolynomialByNaturalArgs` says that an integer-valued function on ℕ eventually agrees with a finite integer combination of the binomial functions n ↦ choose(n, i). The lemmas give a range-sum presentation and closure under eventual equality, addition, negation, subtraction, and the shift n ↦ n − 1.
- `numerical_polynomial_of_difference` proves that f is numerical if n ↦ f(n) − f(n − 1) is numerical. Pascal’s identity constructs a numerical function with the prescribed eventual first difference, and the difference between f and that function is eventually constant.
- `AdmissibleGradedModule` bundles a finitely generated module over a polynomial ring in d variables over a field k, with an independent spanning ℕ-grading by finite-dimensional k-subspaces. Each variable raises degree by one. `AdmissibleGradedModule.hilb` takes the dimension of the degree-n piece as an integer. `AdmissibleGradedModule.hilb_eventually_eq_zero` proves eventual vanishing for d = 0, when a finite-dimensional module has only finitely many nonzero graded pieces.
- `mulXLastDeg` is multiplication by the last variable from degree m to degree m + 1. For an admissible module on d + 1 variables, `exists_kernel_admissible` constructs an admissible module on d variables whose Hilbert value at m is the dimension of the kernel of this degreewise map.

Homogeneity and independence give the kernel its grading. Noetherianity gives finite generation over the original polynomial ring, and the action factors through `qmap`, which sets the last variable to zero.

The admissibility structure is specific to this development. It uses only nonnegative degrees and places the module in the universe of k. The graded-module results here cover the zero-variable case and the kernel step of the induction. A docstring of the file passes to the integer-indexed notion by an extension-by-zero lemma that is not in the file.

References include Tag 00JZ for the natural-argument numerical polynomial and first differences, and Tag 00K1 and Tag 00K2 for the Hilbert-function context.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertFunction/AdmissibleModule.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 40 declarations of the source file 39 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.HilbertFunction.PolynomialQuotient.IsNumericalPolynomialByNaturalArgs.isNumericalPolynomial_extend`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
